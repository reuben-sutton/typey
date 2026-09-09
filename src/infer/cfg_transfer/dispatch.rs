//! Receiver-side dispatch for owned CFG calls.
//!
//! The outer call transfer owns argument materialization and the common
//! normal/abrupt outcome protocol. This layer selects the receiver contract:
//! callable values, declared methods, collection contracts, or primitive
//! builtins. Keeping that choice here makes the dispatch order explicit and
//! leaves the surrounding CFG transfer independent of individual receiver
//! models.

use super::super::hash_shape::HashShape;
use super::super::{
    name_matches, optional_proc_type, proc_parts, Analyzer, CallArguments, Environment, Eval,
    MethodKey, OwnedCallInput, SourceSite, UntypedOrigin,
};
use crate::cfg;
use crate::types::Type;

pub(super) struct ReceiverTransfer {
    pub(super) type_: Type,
    pub(super) block_result: Option<Eval>,
    pub(super) untyped_origin: UntypedOrigin,
    pub(super) missing_method: bool,
}

pub(super) fn transfer_receiver_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
    hash_shape: Option<&HashShape>,
) -> Result<ReceiverTransfer, String> {
    let name = input.name.as_str();
    if name == "singleton_class" {
        return Ok(ReceiverTransfer {
            type_: Type::Named("Class".to_owned(), vec![Type::Anything]),
            block_result: None,
            untyped_origin: UntypedOrigin::DeclaredSignature,
            missing_method: false,
        });
    }
    if matches!(name, "attr_reader" | "attr_writer" | "attr_accessor")
        && Analyzer::class_object_instance_type(receiver).is_some()
    {
        return Ok(ReceiverTransfer {
            type_: Type::Nil,
            block_result: None,
            untyped_origin: UntypedOrigin::DeclaredSignature,
            missing_method: false,
        });
    }
    if !matches!(receiver, Type::Union(_)) {
        if let (Type::Named(class_name, _), Some(instances)) =
            (receiver, Analyzer::class_object_instance_types(receiver))
        {
            if instances.len() > 1 {
                let receiver = Type::Union(
                    instances
                        .into_iter()
                        .map(|instance| Type::Named(class_name.clone(), vec![instance]))
                        .collect(),
                );
                return transfer_receiver_call(
                    analyzer,
                    input,
                    &receiver,
                    arguments,
                    values,
                    environment,
                    hash_shape,
                );
            }
        }
    }
    if let Type::Union(members) = receiver {
        // A union receiver has no single method key. Dispatch each concrete
        // member through the same contract order instead of collapsing the
        // whole receiver to a parser-era fallback. Each member is a separate
        // control-flow path, including when a callback is supplied, so its
        // environment and callback outcomes must be joined rather than
        // applied sequentially.
        let initial_environment = environment.clone();
        let mut result_type = Type::Never;
        let mut block_result = None;
        let mut untyped_origin = UntypedOrigin::Propagated;
        let mut joined_environment: Option<Environment> = None;
        let mut missing_method = false;
        let mut all_members_missing = true;
        for member in members {
            let mut member_environment = initial_environment.clone();
            let result = transfer_receiver_call(
                analyzer,
                input,
                member,
                arguments,
                values,
                &mut member_environment,
                hash_shape,
            )?;
            result_type = result_type.join(&result.type_);
            block_result = match (block_result, result.block_result) {
                (Some(left), Some(right)) => Some(Eval::combine(&left, &right)),
                (left @ Some(_), None) | (None, left @ Some(_)) => left,
                (None, None) => None,
            };
            joined_environment = Some(match joined_environment {
                Some(joined) => joined.join(&member_environment),
                None => member_environment,
            });
            untyped_origin = join_untyped_origin(untyped_origin, result.untyped_origin);
            missing_method |= result.missing_method;
            all_members_missing &= result.missing_method;
        }
        if let Some(joined_environment) = joined_environment {
            *environment = joined_environment;
        }
        if missing_method && all_members_missing {
            analyzer.report_missing_method_if_needed_at(input.site, receiver, name, false);
        }
        return Ok(ReceiverTransfer {
            type_: result_type,
            block_result,
            untyped_origin,
            missing_method: false,
        });
    }
    let callable_type = if matches!(name, "call" | "[]") {
        transfer_callable_call(analyzer, input.site, receiver, arguments)
    } else {
        None
    };
    if let Some(type_) = callable_type {
        return Ok(ReceiverTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
            missing_method: false,
        });
    }
    if let Type::Tuple(elements) = receiver {
        if arguments.argument_types.is_empty() {
            let type_ = match name {
                // A tuple is a fixed-shape Array, so the generic Array RBI
                // contract (`Array::Elem`) is not the right result here.
                // Keep the concrete component just as the recursive
                // dispatcher does for tuple receivers.
                "first" => elements.first().cloned().unwrap_or(Type::Nil),
                "last" => elements.last().cloned().unwrap_or(Type::Nil),
                _ => Type::Never,
            };
            if !type_.is_never() {
                return Ok(ReceiverTransfer {
                    type_,
                    block_result: None,
                    untyped_origin: UntypedOrigin::InferredMethod,
                    missing_method: false,
                });
            }
        }
    }
    if input.safe_navigation && receiver.is_never() {
        return Ok(ReceiverTransfer {
            type_: Type::Nil,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
            missing_method: false,
        });
    }

    if name == "tap" {
        let block_result = match input.block.as_ref() {
            Some(crate::cfg::BlockOperand::Inline(closure)) => analyzer
                .transfer_owned_closure_body(
                    *closure,
                    &[receiver.clone()],
                    None,
                    None,
                    environment,
                ),
            Some(crate::cfg::BlockOperand::Passed(value)) => values
                .get(value.0 as usize)
                .and_then(Option::as_ref)
                .and_then(optional_proc_type)
                .and_then(|block| {
                    super::super::proc_parts(&block).map(|(_, result)| result.clone())
                })
                .map(Eval::value),
            None => None,
        };
        return Ok(ReceiverTransfer {
            type_: receiver.clone(),
            block_result,
            untyped_origin: UntypedOrigin::InferredMethod,
            missing_method: false,
        });
    }

    let helper_type = if analyzer.common_method_helper_shadowed(receiver, name, environment) {
        // An explicit singleton method shadows Kernel#method on a class
        // object. Let the declared method path below handle the collision.
        None
    } else {
        analyzer.eval_node_helpers_method(receiver, name, &arguments.argument_types)
    };
    if let Some(type_) = helper_type {
        return Ok(ReceiverTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::InferredMethod,
            missing_method: false,
        });
    }

    if let Some(result) = analyzer.cfg_dynamic_eval_call(input, receiver, values, environment) {
        let type_ = result.type_.clone();
        return Ok(ReceiverTransfer {
            type_,
            block_result: Some(result),
            untyped_origin: UntypedOrigin::Propagated,
            missing_method: false,
        });
    }

    // Psych's generated gem RBI exposes these methods without useful return
    // signatures. Ruby's `YAML` constant is an alias of `Psych`, so preserve
    // the same concrete standard-library contracts as the recursive path
    // before an untyped declaration can win ordinary method dispatch.
    let psych_receiver = Analyzer::class_object_instance_type(receiver).is_some_and(|instance| {
        Analyzer::named_type_name(&instance)
            .is_some_and(|name| name_matches(&name, "Psych") || name_matches(&name, "YAML"))
    });
    if psych_receiver {
        let type_ = match name {
            "dump" if arguments.argument_types.len() == 1 => Some(Type::String),
            _ => None,
        };
        if let Some(type_) = type_ {
            return Ok(ReceiverTransfer {
                type_,
                block_result: None,
                untyped_origin: UntypedOrigin::FallbackCall,
                missing_method: false,
            });
        }
    }

    if matches!(name, "include" | "prepend" | "extend")
        && Analyzer::class_object_owner(receiver).is_some()
    {
        if let Some(module_name) =
            super::context::owned_mixin_module_name(analyzer, input, environment)
        {
            analyzer.observe_mixin_hook_owned(
                input.site,
                module_name,
                receiver,
                environment,
                name == "extend",
            );
        }
        return Ok(ReceiverTransfer {
            type_: Type::Nil,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
            missing_method: false,
        });
    }

    // `Module#alias_method` mutates the receiver's instance-method table.
    // This is commonly called through an `included` hook, where declaration
    // registration cannot see the receiver or the method names. Record the
    // same alias in the shared method graph so subsequent calls use the real
    // inherited signature instead of falling back to `T.untyped`.
    if name == "alias_method" {
        if let (Some(owner), Some((new_name, old_name))) = (
            Analyzer::class_object_owner(receiver),
            super::builtins::owned_symbol_arguments(analyzer, input),
        ) {
            let new_key = MethodKey {
                owner: Some(owner.clone()),
                name: new_name,
                singleton: false,
            };
            let old_key = MethodKey {
                owner: Some(owner.clone()),
                name: old_name,
                singleton: false,
            };
            let changed = analyzer.declarations.aliases.get(&new_key) != Some(&old_key);
            analyzer.declarations.aliases.insert(new_key, old_key);
            if changed {
                analyzer.method_resolution_cache.borrow_mut().clear();
                analyzer.schedule_method_resolution_dependents(&owner);
            }
            return Ok(ReceiverTransfer {
                type_: Type::Nil,
                block_result: None,
                untyped_origin: UntypedOrigin::Propagated,
                missing_method: false,
            });
        }
    }

    let is_struct_constructor = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
        .and_then(|expression| match &expression.kind {
            crate::hir::ExprKind::Call(call) => match call.receiver {
                crate::hir::Receiver::Explicit(receiver) => analyzer
                    .program
                    .hir_program
                    .expression(receiver)
                    .and_then(|receiver| match &receiver.kind {
                        crate::hir::ExprKind::Read(crate::hir::Read::Constant(name)) => {
                            Some(name.as_str().trim_start_matches("::") == "Struct")
                        }
                        _ => None,
                    }),
                _ => Some(false),
            },
            _ => None,
        })
        .unwrap_or(false);
    if name == "new" && is_struct_constructor {
        analyzer.observe_struct_constructor("Struct", arguments);
        return Ok(ReceiverTransfer {
            type_: Analyzer::class_object_type("Struct"),
            block_result: None,
            untyped_origin: UntypedOrigin::InferredMethod,
            missing_method: false,
        });
    }

    if name == "new" {
        if let Some(instance) = Analyzer::class_object_instance_type(receiver) {
            if let Some(owner) = Analyzer::named_type_name(&instance) {
                let explicit_new = analyzer
                    .resolve_method_key(&MethodKey {
                        owner: Some(owner.clone()),
                        name: name.to_owned(),
                        singleton: true,
                    })
                    .is_some_and(|resolved| resolved.owner.as_deref() == Some(owner.as_str()));
                if !explicit_new {
                    analyzer.infer_initializer_call_at(
                        input.site,
                        &owner,
                        arguments,
                        input.block.is_some(),
                        environment,
                    );
                    analyzer.observe_struct_constructor(&owner, arguments);
                    return Ok(ReceiverTransfer {
                        type_: analyzer.instantiate_generic_class(instance),
                        block_result: None,
                        untyped_origin: UntypedOrigin::InferredMethod,
                        missing_method: false,
                    });
                }
            }
        }
        if let Some(owner) = Analyzer::named_type_name(receiver)
            .filter(|owner| analyzer.declarations.struct_fields.contains_key(owner))
        {
            analyzer.infer_initializer_call_at(
                input.site,
                &owner,
                arguments,
                input.block.is_some(),
                environment,
            );
            analyzer.observe_struct_constructor(&owner, arguments);
            return Ok(ReceiverTransfer {
                type_: Type::named(owner),
                block_result: None,
                untyped_origin: UntypedOrigin::InferredMethod,
                missing_method: false,
            });
        }
    }

    // A literal hash carries a flow-local key/value refinement alongside its
    // aggregate `Type::Hash`. Use that refinement before ordinary RBI method
    // lookup, whose generic `Hash#[]` contract necessarily loses the key.
    if name == "[]" && matches!(receiver, Type::Hash(_, _)) {
        if let Some(hash_shape) = hash_shape {
            if let Some(key) = super::builtins::owned_hash_key(analyzer, input) {
                return Ok(ReceiverTransfer {
                    type_: hash_shape.value_for(&key),
                    block_result: None,
                    untyped_origin: UntypedOrigin::Propagated,
                    missing_method: false,
                });
            }
        }
    }

    // Array indexing is partial even when the core RBI supplies a declared
    // overload. Prefer the structural contract so an integer index retains
    // its nilable result instead of trusting a generic summary that loses the
    // out-of-bounds path.
    if matches!(name, "[]" | "<=>") && matches!(receiver, Type::Array(_) | Type::Tuple(_)) {
        if let Some((type_, block_result)) = super::builtins::transfer_builtin_call(
            analyzer,
            input,
            receiver,
            arguments,
            values,
            environment,
            hash_shape,
        ) {
            return Ok(ReceiverTransfer {
                type_,
                block_result,
                untyped_origin: UntypedOrigin::FallbackCall,
                missing_method: false,
            });
        }
    }

    // `[]` is also ordinary Ruby method dispatch. Only proc-like receivers
    // use the callable shorthand; a nominal receiver must still resolve its
    // declared `[]` method here.
    if name == "[]" {
        if let Some(instance) = Analyzer::class_object_instance_type(receiver) {
            if let Some(type_arguments) = arguments
                .argument_types
                .iter()
                .map(Analyzer::class_object_value_type)
                .collect::<Option<Vec<_>>>()
            {
                let type_ = match &instance {
                    Type::Named(owner, _)
                        if matches!(owner.as_str(), "Array" | "T::Array")
                            && type_arguments.len() == 1 =>
                    {
                        Type::Array(Box::new(type_arguments[0].clone()))
                    }
                    Type::Named(owner, _)
                        if matches!(owner.as_str(), "Hash" | "T::Hash")
                            && type_arguments.len() == 2 =>
                    {
                        Type::Hash(
                            Box::new(type_arguments[0].clone()),
                            Box::new(type_arguments[1].clone()),
                        )
                    }
                    Type::Named(owner, _) => Type::Named(owner.clone(), type_arguments),
                    _ => {
                        return Err(format!(
                            "receiver call `{name}` on `{receiver}` has no generic type contract"
                        ))
                    }
                };
                return Ok(ReceiverTransfer {
                    type_,
                    block_result: None,
                    untyped_origin: UntypedOrigin::Propagated,
                    missing_method: false,
                });
            }
        }
    }

    // `Random.alphanumeric` and `SecureRandom.alphanumeric` are documented
    // by the core RBI with an incomplete implementation shape. The recursive
    // dispatcher supplies the optional length/keyword contract explicitly;
    // keep owned CFG calls on that same contract instead of reporting the
    // Ruby implementation's internal forwarding call as an arity error.
    if let Some(signature) = analyzer.random_formatter_signature(None, receiver, name) {
        let type_ = analyzer.invoke_signature_at(
            input.site,
            name,
            &signature,
            arguments,
            Some(receiver),
            None,
        );
        return Ok(ReceiverTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::InferredMethod,
            missing_method: false,
        });
    }

    // Struct accessors are generated from the fields observed at construction
    // time. Resolve them before the ordinary method table: a broad RBI method
    // entry must not erase the concrete field contract.
    if let Some(owner) = Analyzer::named_type_name(receiver) {
        if let Some(type_) = analyzer.struct_field_type(&owner, name, environment) {
            return Ok(ReceiverTransfer {
                type_,
                block_result: None,
                untyped_origin: UntypedOrigin::InferredMethod,
                missing_method: false,
            });
        }
    }

    let key = analyzer.receiver_method_key(None, receiver, name, environment);
    if let Some(key) = key {
        analyzer.record_method_dependency(&key, environment);
        let inferred_accessor = analyzer
            .resolve_method_key(&key)
            .filter(|resolved| {
                analyzer
                    .declarations
                    .methods
                    .get(resolved)
                    .is_some_and(|state| !state.explicit)
            })
            .and_then(|resolved| {
                analyzer
                    .declarations
                    .accessors
                    .get(&resolved)
                    .copied()
                    .map(|accessor| (resolved, accessor))
            });
        if let Some((accessor_key, accessor)) = inferred_accessor {
            let type_ = analyzer.eval_accessor_call(
                &accessor_key,
                accessor,
                &arguments.argument_types,
                environment,
            );
            return Ok(ReceiverTransfer {
                type_,
                block_result: None,
                untyped_origin: UntypedOrigin::InferredMethod,
                missing_method: false,
            });
        }
        if let Some(signature) = analyzer
            .observe_call(&key, arguments, input.block.is_some())
            .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
        {
            let block_result = analyzer.cfg_block_return_type(
                input,
                &key,
                &signature,
                arguments,
                receiver,
                values,
                environment,
            );
            let block_return_type = block_result.as_ref().map(Analyzer::block_value_type);
            let type_ = analyzer.invoke_signature_at(
                input.site,
                name,
                &signature,
                arguments,
                Some(receiver),
                block_return_type.as_ref(),
            );
            let type_ = if name == "new" {
                let type_ = analyzer.instantiate_generic_class(type_);
                analyzer.default_class_constructor_type(receiver, type_)
            } else {
                type_
            };
            let untyped_origin = analyzer
                .resolve_method_key(&key)
                .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                .is_some_and(|state| state.explicit)
                .then_some(UntypedOrigin::DeclaredSignature)
                .unwrap_or(UntypedOrigin::InferredMethod);
            return Ok(ReceiverTransfer {
                type_,
                block_result,
                untyped_origin,
                missing_method: false,
            });
        }
    }

    // If no Psych declaration was available, retain the recursive path's
    // gradual fallback for dynamically shaped YAML documents. An explicit
    // Psych RBI method has already returned above, so this does not turn an
    // intentionally untyped declaration into a spurious nilability error.
    if psych_receiver && matches!(name, "load" | "load_file") {
        return Ok(ReceiverTransfer {
            type_: Type::union([Type::Nil, Type::Object]),
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
            missing_method: false,
        });
    }

    if let Some(owner) = Analyzer::named_type_name(receiver) {
        if let Some(type_) = analyzer.inferred_accessor_ivar_type(&owner, name, false, environment)
        {
            return Ok(ReceiverTransfer {
                type_,
                block_result: None,
                untyped_origin: UntypedOrigin::InferredMethod,
                missing_method: false,
            });
        }
    }

    if let Some((type_, block_result)) =
        super::collections::transfer_collection_call(analyzer, input, receiver, values, environment)
    {
        return Ok(ReceiverTransfer {
            type_,
            block_result,
            untyped_origin: UntypedOrigin::FallbackCall,
            missing_method: false,
        });
    }
    if let Some((type_, block_result)) = super::builtins::transfer_builtin_call(
        analyzer,
        input,
        receiver,
        arguments,
        values,
        environment,
        hash_shape,
    ) {
        return Ok(ReceiverTransfer {
            type_,
            block_result,
            untyped_origin: if receiver.is_any() {
                UntypedOrigin::Propagated
            } else {
                UntypedOrigin::FallbackCall
            },
            missing_method: false,
        });
    }

    // The remaining T.* contracts still have parser-backed metatype and
    // annotation semantics. Keep those calls on the transactional migration
    // boundary until their owned representation is complete; treating an
    // unsupported intrinsic as an ordinary missing application method would
    // lose reveal/type-expression diagnostics.
    if matches!(receiver, Type::Named(name, _) if name == "T" || name.starts_with("T::Types::"))
        || Analyzer::class_object_instance_type(receiver)
            .is_some_and(|instance| matches!(instance, Type::Named(name, _) if name == "T"))
    {
        return Err(format!("intrinsic `{name}` has no owned contract"));
    }

    let block_result = match input.block.as_ref() {
        Some(cfg::BlockOperand::Inline(closure)) => {
            // Ruby type-checks an inline block even when the receiver's method
            // is dynamic. There is no contract to specialize its parameters,
            // but the owned body still needs to be visited so its sends and
            // diagnostics are not silently lost behind T.untyped dispatch.
            analyzer.transfer_owned_closure_body(*closure, &[Type::Any], None, None, environment)
        }
        Some(cfg::BlockOperand::Passed(_)) | None => None,
    };
    Ok(ReceiverTransfer {
        type_: Type::Any,
        block_result,
        untyped_origin: UntypedOrigin::FallbackCall,
        missing_method: true,
    })
}

fn join_untyped_origin(left: UntypedOrigin, right: UntypedOrigin) -> UntypedOrigin {
    if left == UntypedOrigin::FallbackCall || right == UntypedOrigin::FallbackCall {
        UntypedOrigin::FallbackCall
    } else if left == UntypedOrigin::DeclaredSignature || right == UntypedOrigin::DeclaredSignature
    {
        UntypedOrigin::DeclaredSignature
    } else if left == UntypedOrigin::InferredMethod || right == UntypedOrigin::InferredMethod {
        UntypedOrigin::InferredMethod
    } else {
        UntypedOrigin::Propagated
    }
}

pub(super) fn transfer_callable_call(
    analyzer: &mut Analyzer<'_>,
    site: SourceSite,
    receiver: &Type,
    arguments: &CallArguments<'_>,
) -> Option<Type> {
    match receiver {
        Type::Proc(_, _) | Type::BoundProc { .. } => {
            let (parameters, result) = proc_parts(receiver)?;
            for (index, (actual, expected)) in
                arguments.argument_types.iter().zip(parameters).enumerate()
            {
                if !analyzer.is_assignable(actual, expected) {
                    let argument_site =
                        arguments.argument_sites.get(index).copied().unwrap_or(site);
                    analyzer.error_at(
                        argument_site,
                        format!(
                            "Expected `{expected}` but found `{actual}` for argument `arg{index}"
                        ),
                    );
                }
            }
            Some(result.clone())
        }
        Type::Union(members)
            if members.iter().all(|member| {
                member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
            }) =>
        {
            let mut result = Type::Never;
            for member in members {
                if !member.is_nil() {
                    result =
                        result.join(&transfer_callable_call(analyzer, site, member, arguments)?);
                }
            }
            Some(if result.is_never() { Type::Any } else { result })
        }
        _ => None,
    }
}
