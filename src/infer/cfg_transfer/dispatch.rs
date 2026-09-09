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
    proc_parts, Analyzer, CallArguments, Environment, Eval, MethodKey, OwnedCallInput, SourceSite,
    UntypedOrigin,
};
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
        }
        if let Some(joined_environment) = joined_environment {
            *environment = joined_environment;
        }
        if missing_method {
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
    if input.safe_navigation && receiver.is_never() {
        return Ok(ReceiverTransfer {
            type_: Type::Nil,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
            missing_method: false,
        });
    }

    if let Some(type_) =
        analyzer.eval_node_helpers_method(receiver, name, &arguments.argument_types)
    {
        return Ok(ReceiverTransfer {
            type_,
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
    let key = analyzer.receiver_method_key(None, receiver, name, environment);
    if let Some(key) = key {
        analyzer.record_method_dependency(&key, environment);
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

    if let Some(owner) = Analyzer::named_type_name(receiver) {
        if let Some(type_) = analyzer.struct_field_type(&owner, name, environment) {
            return Ok(ReceiverTransfer {
                type_,
                block_result: None,
                untyped_origin: UntypedOrigin::InferredMethod,
                missing_method: false,
            });
        }
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

    Ok(ReceiverTransfer {
        type_: Type::Any,
        block_result: None,
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
