//! Receiver-side dispatch for owned CFG calls.
//!
//! The outer call transfer owns argument materialization and the common
//! normal/abrupt outcome protocol. This layer selects the receiver contract:
//! callable values, declared methods, collection contracts, or primitive
//! builtins. Keeping that choice here makes the dispatch order explicit and
//! leaves the surrounding CFG transfer independent of individual receiver
//! models.

use super::super::declarations::Visibility;
use super::super::hash_shape::HashShape;
use super::super::{
    name_matches, optional_proc_type, proc_parts, Analyzer, CallArguments, Environment, Eval,
    MethodKey, OwnedCallInput, SourceSite, UntypedOrigin,
};
use crate::cfg;
use crate::hir;
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
    transfer_receiver_call_with_substitution(
        analyzer,
        input,
        receiver,
        receiver,
        arguments,
        values,
        environment,
        hash_shape,
    )
}

fn transfer_receiver_call_with_substitution(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    substitution_receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
    hash_shape: Option<&HashShape>,
) -> Result<ReceiverTransfer, String> {
    let name = input.name.as_str();
    if name == "class" {
        let class_name = match receiver {
            Type::Array(_) | Type::Tuple(_) => Some("Array"),
            Type::Hash(_, _) => Some("Hash"),
            Type::Named(class, _) if name_matches(class, "Array") => Some("Array"),
            Type::Named(class, _) if name_matches(class, "Hash") => Some("Hash"),
            _ => None,
        };
        if let Some(class_name) = class_name {
            return Ok(ReceiverTransfer {
                type_: Analyzer::class_object_type(class_name),
                block_result: None,
                untyped_origin: UntypedOrigin::InferredMethod,
                missing_method: false,
            });
        }
    }
    if let Some(type_) = analyzer.owned_framework_call_type(receiver, name) {
        return Ok(ReceiverTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::InferredMethod,
            missing_method: false,
        });
    }
    if name == "singleton_class" {
        return Ok(ReceiverTransfer {
            type_: Type::Named("Class".to_owned(), vec![Type::Anything]),
            block_result: None,
            untyped_origin: UntypedOrigin::DeclaredSignature,
            missing_method: false,
        });
    }
    if Analyzer::class_object_instance_type(receiver).is_some_and(|instance| {
        Analyzer::named_type_name(&instance).is_some_and(|name| name_matches(&name, "Ractor"))
    }) && matches!(name, "[]" | "[]=")
    {
        // Ruby exposes Ractor's storage operators as singleton methods. The
        // vendored stdlib RBI currently places their contracts on the
        // instance class, so resolve the runtime class-object form here.
        return Ok(ReceiverTransfer {
            type_: Type::Any,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
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
        let optional_callable = matches!(name, "call" | "[]")
            && members
                .iter()
                .any(|member| matches!(member, Type::Proc(_, _) | Type::BoundProc { .. }))
            && members.iter().all(|member| {
                member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
            });
        let optional_proc_arity = name == "arity"
            && members
                .iter()
                .any(|member| matches!(member, Type::Proc(_, _) | Type::BoundProc { .. }))
            && members.iter().all(|member| {
                member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
            });
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
        let mut missing_members = Vec::new();
        for member in members {
            // Calling an optional block is a normal-path operation on the
            // callable member. The nil member raises at runtime and must not
            // turn the valid callable path into an untyped method lookup.
            if (optional_callable || optional_proc_arity) && member.is_nil() {
                continue;
            }
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
            if result.missing_method {
                missing_members.push(member.clone());
            }
        }
        if let Some(joined_environment) = joined_environment {
            *environment = joined_environment;
        }
        if missing_method {
            if all_members_missing {
                analyzer.report_missing_method_if_needed_at(input.site, receiver, name, false);
            } else {
                for member in missing_members {
                    analyzer.report_missing_method_component_if_needed_at(
                        input.site, &member, name, receiver,
                    );
                }
            }
        }
        return Ok(ReceiverTransfer {
            type_: result_type,
            block_result,
            untyped_origin,
            missing_method: false,
        });
    }
    // Sorbet prints both runtime arrays and generic type expressions as
    // `T::Array[Elem]`. The type parser keeps the latter nominal so it can
    // preserve the source spelling, but instance dispatch still needs the
    // structural Array contract. Normalize only the receiver used for this
    // call; do not change the public type representation.
    if let Some(structural) = structural_collection_receiver(receiver) {
        return transfer_receiver_call(
            analyzer,
            input,
            &structural,
            arguments,
            values,
            environment,
            hash_shape,
        );
    }

    if name == "arity" && matches!(receiver, Type::Proc(_, _) | Type::BoundProc { .. }) {
        return Ok(ReceiverTransfer {
            type_: Type::Integer,
            block_result: None,
            untyped_origin: UntypedOrigin::InferredMethod,
            missing_method: false,
        });
    }

    // Intersections represent one value satisfying several contracts. Search
    // each member for a method, ignoring members which do not contribute that
    // method, and retain the original receiver for attached-class substitution.
    if let Type::Intersection(members) = receiver {
        if let Some(result) = transfer_intersection_members(
            analyzer,
            input,
            members.iter().cloned(),
            substitution_receiver,
            arguments,
            values,
            environment,
            hash_shape,
        )? {
            return Ok(result);
        }
    }

    // An intersection inside a class object represents one runtime class
    // satisfying several interfaces, not a union of unrelated class objects.
    // Look up the singleton method on each intersected instance while
    // retaining the original class-object type for attached-class substitution.
    if let Type::Named(class, type_arguments) = receiver {
        if (name_matches(class, "Class") || name_matches(class, "Module"))
            && type_arguments
                .first()
                .is_some_and(|argument| matches!(argument, Type::Intersection(_)))
        {
            let Some(Type::Intersection(members)) = type_arguments.first() else {
                unreachable!("checked class-object intersection");
            };
            let candidates = members
                .iter()
                .cloned()
                .map(|member| Type::Named(class.clone(), vec![member]));
            if let Some(result) = transfer_intersection_members(
                analyzer,
                input,
                candidates,
                substitution_receiver,
                arguments,
                values,
                environment,
                hash_shape,
            )? {
                return Ok(result);
            }
        }
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
    if name == "binding" && matches!(receiver, Type::Proc(_, _) | Type::BoundProc { .. }) {
        return Ok(ReceiverTransfer {
            type_: Type::named("Binding"),
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
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

    // Several standard-library classes have generic RBI entries whose
    // unresolved type variables are less precise than their concrete runtime
    // contracts. Prefer the owned structural model before common helper
    // methods (such as `to_a`) or ordinary method lookup can publish that
    // unresolved result.
    let standard_builtin_receiver = matches!(
        receiver,
        Type::Named(class, _)
            if name_matches(class, "Range")
                || name_matches(class, "Regexp")
                || name_matches(class, "OptionParser")
                || name_matches(class, "Parser::Source::Map")
                || name_matches(class, "Parser::Source::Range")
                || name_matches(class, "Parser::AST::Node")
                || name_matches(class, "REXML::Element")
                || name_matches(class, "REXML::Document")
    ) || matches!(
        receiver,
        Type::Array(_) | Type::Tuple(_) | Type::Hash(_, _)
    ) || matches!(receiver, Type::Named(class, _) if analyzer.nominal_subtype(class, "TSort"))
        || Analyzer::class_object_instance_type(receiver).is_some_and(|instance| {
            matches!(instance, Type::Named(class, _) if analyzer.nominal_subtype(&class, "Thor"))
        });
    if standard_builtin_receiver {
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

    if name == "const_get" {
        if let Some(instance) = Analyzer::class_object_instance_type(receiver) {
            let owner = Analyzer::named_type_name(&instance);
            let constant_name = owned_constant_name(analyzer, input);
            if let (Some(owner), Some(constant_name)) = (owner, constant_name) {
                let resolved = analyzer.resolve_name(
                    &constant_name,
                    (!constant_name.starts_with("::")).then_some(owner.as_str()),
                );
                if analyzer.declarations.classes.contains_key(&resolved) {
                    return Ok(ReceiverTransfer {
                        type_: Analyzer::class_object_type(&resolved),
                        block_result: None,
                        untyped_origin: UntypedOrigin::InferredMethod,
                        missing_method: false,
                    });
                }
                if let Some(type_) = analyzer.declarations.constants.get(&resolved).cloned() {
                    return Ok(ReceiverTransfer {
                        type_: analyzer.resolve_type_names(&type_, Some(&owner)),
                        block_result: None,
                        untyped_origin: UntypedOrigin::InferredMethod,
                        missing_method: false,
                    });
                }
            }
            return Ok(ReceiverTransfer {
                type_: Type::Object,
                block_result: None,
                untyped_origin: UntypedOrigin::FallbackCall,
                missing_method: false,
            });
        }
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
            if matches!(&instance, Type::Named(owner, _) if name_matches(owner, "Set"))
                && (arguments.argument_types.first().is_some() || input.block.is_some())
            {
                let source_element = arguments
                    .argument_types
                    .first()
                    .map(|argument| analyzer.array_element_type(argument))
                    .unwrap_or(Type::Any);
                let element = input
                    .block
                    .as_ref()
                    .and_then(|_| {
                        analyzer
                            .cfg_owned_block_return_type(
                                input,
                                std::slice::from_ref(&source_element),
                                &Type::Anything,
                                values,
                                environment,
                            )
                            .map(|result| Analyzer::block_value_type(&result))
                    })
                    .unwrap_or(source_element);
                return Ok(ReceiverTransfer {
                    type_: Type::Named("Set".to_owned(), vec![element]),
                    block_result: None,
                    untyped_origin: UntypedOrigin::InferredMethod,
                    missing_method: false,
                });
            }
            // `Class.new(Superclass) { ... }` creates a new class object whose
            // block executes with that class as `self`.  The generic
            // `Class#new` contract would otherwise construct `Class` itself
            // and lose the inherited singleton methods visible in the block.
            if Analyzer::named_type_name(&instance).is_some_and(|name| name_matches(&name, "Class"))
            {
                if let Some(cfg::BlockOperand::Inline(_)) = input.block.as_ref() {
                    let superclass = arguments.argument_types.first();
                    let class_object = analyzer.anonymous_class_object_type(input.site, superclass);
                    let block_result = match input.block.as_ref() {
                        Some(cfg::BlockOperand::Inline(closure)) => analyzer
                            .transfer_owned_closure_body(
                                *closure,
                                &[],
                                None,
                                Some(&class_object),
                                environment,
                            ),
                        Some(cfg::BlockOperand::Passed(_)) | None => None,
                    };
                    return Ok(ReceiverTransfer {
                        type_: class_object,
                        block_result,
                        untyped_origin: UntypedOrigin::InferredMethod,
                        missing_method: false,
                    });
                }
            }
            if instance.is_any() || matches!(instance, Type::Anything) {
                return Ok(ReceiverTransfer {
                    type_: instance,
                    block_result: None,
                    untyped_origin: UntypedOrigin::Propagated,
                    missing_method: false,
                });
            }
            if let Some(owner) = Analyzer::named_type_name(&instance) {
                let block_result = if name_matches(&owner, "OptionParser") {
                    match input.block.as_ref() {
                        Some(cfg::BlockOperand::Inline(closure)) => analyzer
                            .transfer_owned_closure_body(
                                *closure,
                                std::slice::from_ref(&instance),
                                None,
                                None,
                                environment,
                            ),
                        Some(cfg::BlockOperand::Passed(_)) | None => None,
                    }
                } else {
                    None
                };
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
                    let type_ = if name == "new"
                        && cfg_explicit_self_receiver(analyzer, input)
                        && environment
                            .method_key
                            .as_ref()
                            .is_some_and(|key| key.singleton)
                    {
                        Type::AttachedClassOf(owner.clone())
                    } else {
                        analyzer.instantiate_generic_class(instance)
                    };
                    return Ok(ReceiverTransfer {
                        type_,
                        block_result,
                        untyped_origin: UntypedOrigin::InferredMethod,
                        missing_method: false,
                    });
                }
            }
        }
        // A generic instance such as `Box[String]` can use its own type
        // arguments when constructing a value. Class objects such as
        // `Class[Proc]` also have a named type argument, but must continue to
        // ordinary singleton dispatch so `Proc.new` returns `Proc` rather
        // than the class-object type itself.
        if Analyzer::class_object_instance_type(receiver).is_none() {
            if let Type::Named(owner, type_arguments) = receiver {
                if !type_arguments.is_empty()
                    && analyzer
                        .declarations
                        .classes
                        .get(owner)
                        .is_some_and(|info| !info.type_members.is_empty())
                {
                    analyzer.infer_initializer_call_at(
                        input.site,
                        owner,
                        arguments,
                        input.block.is_some(),
                        environment,
                    );
                    return Ok(ReceiverTransfer {
                        type_: receiver.clone(),
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
    // An explicitly gradual hash contract is an information boundary. A
    // literal shape may know more about the initializer, but callers of
    // `Hash[K, untyped]` must observe the declared value type rather than a
    // union reconstructed from the current literal entries. Otherwise an
    // annotated options hash can spuriously reject ordinary calls such as
    // `options[:paths].empty?`.
    if name == "[]" && matches!(receiver, Type::Hash(_, value) if !value.is_any()) {
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
    if matches!(
        name,
        "[]" | "<=>" | "min" | "max" | "push" | "<<" | "prepend"
    ) && matches!(receiver, Type::Array(_) | Type::Tuple(_))
    {
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

    // The core RBI describes String#[] as nilable for arbitrary indices. A
    // path which has already proved a String non-empty makes an integer index
    // total, however. Apply that structural refinement before the generic RBI
    // declaration so a loaded core contract cannot erase the flow fact.
    if name == "[]"
        && matches!(receiver, Type::String)
        && arguments.argument_types.first() == Some(&Type::Integer)
        && super::builtins::known_nonempty_string_receiver(analyzer, input, environment)
    {
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
            let type_arguments = arguments
                .argument_types
                .iter()
                .map(|argument| {
                    Analyzer::class_object_value_type(argument).unwrap_or_else(|| argument.clone())
                })
                .collect::<Vec<_>>();
            let runtime_constructor = matches!(
                &instance,
                Type::Named(owner, _) if name_matches(owner, "Hash") || name_matches(owner, "Dir")
            );
            if is_generic_type_application(analyzer, input) || runtime_constructor {
                // Preserve generic type application for `T::Set[...]` and
                // similar nominal expressions. Runtime collection
                // constructors retain their structural contracts, while an
                // unrelated `Constant[...]` reaches ordinary singleton
                // signature dispatch (important for APIs such as
                // `IsolatedExecutionState[:key]`).
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
                    Type::Named(owner, _)
                        if matches!(owner.as_str(), "Hash" | "T::Hash")
                            && type_arguments.len() == 1 =>
                    {
                        let (key, value) = hash_constructor_pair_types(&type_arguments[0])
                            .unwrap_or((Type::Any, Type::Any));
                        Type::Hash(Box::new(key), Box::new(value))
                    }
                    Type::Named(owner, _) if name_matches(owner, "Dir") => {
                        Type::Array(Box::new(Type::String))
                    }
                    Type::Named(owner, _) => Type::Named(owner.clone(), type_arguments),
                    _ => {
                        return Err(format!(
                            "receiver call `{name}` on `{receiver}` has no generic type contract"
                        ))
                    }
                };
                let untyped_origin = if type_.contains_any() {
                    UntypedOrigin::FallbackCall
                } else {
                    UntypedOrigin::Propagated
                };
                return Ok(ReceiverTransfer {
                    type_,
                    block_result: None,
                    untyped_origin,
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
    if let Some(signature) = analyzer.random_formatter_signature(receiver, name) {
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

    // Core primitive operators can have provisional inferred declarations in
    // the shared method table. Those declarations start at `T.noreturn` and
    // would make a later fixpoint pass treat an otherwise ordinary operation
    // such as `Integer#+` as an unconditional raise. Use the structural
    // primitive contract until an explicit user/RBI signature is available;
    // explicit contracts still retain normal precedence.
    let primitive_operator = matches!(
        receiver,
        Type::Nil
            | Type::True
            | Type::False
            | Type::Integer
            | Type::Float
            | Type::String
            | Type::Symbol
    ) && matches!(
        name,
        "+" | "-" | "*" | "/" | "%" | "<=>" | "==" | "!=" | "<" | "<=" | ">" | ">="
    );
    let primitive_has_explicit_contract = analyzer
        .receiver_method_key(None, receiver, name, environment)
        .and_then(|key| analyzer.resolve_method_key(&key))
        .and_then(|key| analyzer.declarations.methods.get(&key))
        .is_some_and(|state| state.explicit);
    if primitive_operator && !primitive_has_explicit_contract {
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

    let key = analyzer.receiver_method_key(None, receiver, name, environment);
    if let Some(key) = key {
        analyzer.record_method_dependency(&key, environment);
        if analyzer
            .resolve_method_key(&key)
            .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
            .is_some_and(|state| state.visibility == Visibility::Private)
            && !matches!(input.receiver, cfg::ReceiverOperand::Implicit)
            && !analyzer.private_call_allowed(&key, environment)
        {
            analyzer.error_at(
                input.site,
                format!("Non-private call to private method `{name}` on `{receiver}`"),
            );
            return Ok(ReceiverTransfer {
                type_: Type::Any,
                block_result: None,
                untyped_origin: UntypedOrigin::FallbackCall,
                missing_method: false,
            });
        }
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
            .map(|signature| analyzer.widen_overridable_literal_return(&key, signature))
        {
            let block_result = analyzer.cfg_block_return_type(
                input,
                &key,
                &signature,
                arguments,
                substitution_receiver,
                values,
                environment,
            );
            let block_return_type = block_result.as_ref().map(Analyzer::block_value_type);
            let type_ = analyzer.invoke_signature_at(
                input.site,
                name,
                &signature,
                arguments,
                Some(substitution_receiver),
                block_return_type.as_ref(),
            );
            let type_ = analyzer.widen_recursive_call_return(&key, type_, environment);
            let type_ = if name == "new" {
                let type_ = analyzer.instantiate_generic_class(type_);
                analyzer.default_class_constructor_type(substitution_receiver, type_)
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
            untyped_origin: if input.name.as_str() == "new" || receiver.is_any() {
                UntypedOrigin::Propagated
            } else {
                UntypedOrigin::FallbackCall
            },
            missing_method: false,
        });
    }

    // `respond_to?` is a runtime capability guard. If the guarded method is
    // absent from the static declaration graph, the call is still valid on
    // that path (for example through `method_missing` or a parser source-map
    // subclass). Keep the result gradual because the guard proves presence,
    // not the method's return contract.
    if cfg_respond_to_guard(analyzer, input, environment, name) {
        return Ok(ReceiverTransfer {
            type_: Type::Any,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
            missing_method: false,
        });
    }

    // An unhandled call on Sorbet's runtime type objects is still a checked
    // call. Intrinsic constructors have already been handled above; an
    // operation such as `T.proc.call` must not disappear behind an internal
    // transfer error.
    if matches!(receiver, Type::Named(name, _) if name == "T" || name.starts_with("T::Types::"))
        || Analyzer::class_object_instance_type(receiver)
            .is_some_and(|instance| matches!(instance, Type::Named(name, _) if name == "T"))
    {
        return Ok(ReceiverTransfer {
            type_: Type::Any,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
            missing_method: true,
        });
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

fn cfg_respond_to_guard(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    environment: &Environment,
    method: &str,
) -> bool {
    let Some(expression) = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
    else {
        return false;
    };
    let crate::hir::ExprKind::Call(call) = &expression.kind else {
        return false;
    };
    let crate::hir::Receiver::Explicit(receiver) = call.receiver else {
        return false;
    };
    let Some(receiver) = analyzer.program.hir_program.expression(receiver) else {
        return false;
    };
    let Some(key) = (match &receiver.kind {
        crate::hir::ExprKind::Read(crate::hir::Read::Local(local)) => analyzer
            .program
            .hir_program
            .local_name(*local)
            .map(|name| format!("\u{1}local:{name}")),
        crate::hir::ExprKind::Read(crate::hir::Read::InstanceVariable(name)) => {
            Some(format!("\u{1}ivar:{name}"))
        }
        _ => None,
    }) else {
        return false;
    };
    environment.known_respond_to(&key, method)
}

fn is_generic_type_application(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> bool {
    let Some(expression) = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
    else {
        return false;
    };
    let crate::hir::ExprKind::Call(call) = &expression.kind else {
        return false;
    };
    let crate::hir::Receiver::Explicit(receiver) = call.receiver else {
        return false;
    };
    let Some(crate::hir::ExprKind::Read(crate::hir::Read::Constant(name))) = analyzer
        .program
        .hir_program
        .expression(receiver)
        .map(|receiver| &receiver.kind)
    else {
        return false;
    };
    let name = name.as_str().trim_start_matches("::");
    if name.starts_with("T::") {
        return true;
    }
    if analyzer
        .declarations
        .classes
        .get(name)
        .is_some_and(|info| !info.type_members.is_empty())
    {
        // A class which declares Sorbet generic members uses `Foo[T]` as a
        // type application when it has no runtime singleton `[]`. If the
        // class does define that method, however, the same syntax is an
        // ordinary Ruby constructor call (for example `Set["one"]`) and its
        // declared signature must win over the generic-type shorthand.
        let runtime_key = MethodKey {
            owner: Some(name.to_owned()),
            name: "[]".to_owned(),
            singleton: true,
        };
        if analyzer.resolve_method_key(&runtime_key).is_none() {
            return true;
        }
    }

    // Bare generic applications such as `Enumerator[Integer]` occur inside
    // Sorbet type expressions (`T.any`, `T.let`, `T.cast`, ...). The same
    // syntax is also a normal Ruby class-method call, so inspect the owned
    // HIR spans of the enclosing T type argument instead of treating every
    // `Constant[]` as a generic constructor.
    analyzer
        .program
        .hir_program
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            crate::hir::ExprKind::Call(call) => Some(call),
            _ => None,
        })
        .any(|parent| {
            let crate::hir::Receiver::Explicit(parent_receiver) = parent.receiver else {
                return false;
            };
            let is_type_intrinsic = analyzer
                .program
                .hir_program
                .expression(parent_receiver)
                .and_then(|receiver| match &receiver.kind {
                    crate::hir::ExprKind::Read(crate::hir::Read::Constant(name)) => Some(
                        name.as_str().trim_start_matches("::") == "T"
                            && matches!(
                                parent.name.as_str(),
                                "any" | "all" | "nilable" | "let" | "cast" | "assert_type!"
                            ),
                    ),
                    _ => None,
                })
                .unwrap_or(false);
            if !is_type_intrinsic {
                return false;
            }
            let positional_arguments = parent
                .arguments
                .iter()
                .filter_map(|argument| {
                    let crate::hir::Argument::Positional(argument) = argument else {
                        return None;
                    };
                    analyzer.program.hir_program.expression(*argument)
                })
                .collect::<Vec<_>>();
            let type_arguments = if matches!(parent.name.as_str(), "let" | "cast" | "assert_type!")
            {
                positional_arguments.get(1..).unwrap_or_default()
            } else {
                positional_arguments.as_slice()
            };
            type_arguments.iter().any(|argument| {
                expression.span.start >= argument.span.start
                    && expression.span.end <= argument.span.end
            })
        })
}

fn cfg_explicit_self_receiver(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> bool {
    let Some(expression) = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
    else {
        return false;
    };
    let hir::ExprKind::Call(call) = &expression.kind else {
        return false;
    };
    let hir::Receiver::Explicit(receiver) = call.receiver else {
        return false;
    };
    matches!(
        analyzer.program.hir_program.expression(receiver),
        Some(hir::Expr {
            kind: hir::ExprKind::Read(hir::Read::SelfValue),
            ..
        })
    )
}

fn owned_constant_name(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> Option<String> {
    let expression = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))?;
    let crate::hir::ExprKind::Call(call) = &expression.kind else {
        return None;
    };
    let crate::hir::Argument::Positional(argument) = call.arguments.first()? else {
        return None;
    };
    let expression = analyzer.program.hir_program.expression(*argument)?;
    match &expression.kind {
        crate::hir::ExprKind::Literal(crate::hir::Literal::Symbol(name)) => Some(name.clone()),
        crate::hir::ExprKind::Literal(crate::hir::Literal::String(name)) => Some(name.clone()),
        _ => None,
    }
}

fn hash_constructor_pair_types(type_: &Type) -> Option<(Type, Type)> {
    if let Type::Tuple(elements) = type_ {
        let pairs = elements
            .iter()
            .map(Analyzer::pair_types)
            .collect::<Option<Vec<_>>>();
        if let Some(mut pairs) = pairs.filter(|pairs| !pairs.is_empty()) {
            let (mut key, mut value) = pairs.remove(0);
            for (next_key, next_value) in pairs {
                key = key.join(&next_key);
                value = value.join(&next_value);
            }
            return Some((key, value));
        }
    }
    Analyzer::pair_types(type_)
}

fn transfer_intersection_members<I>(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    candidates: I,
    substitution_receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
    hash_shape: Option<&HashShape>,
) -> Result<Option<ReceiverTransfer>, String>
where
    I: IntoIterator<Item = Type>,
{
    let initial_environment = environment.clone();
    let mut result_type = Type::Never;
    let mut block_result = None;
    let mut untyped_origin = UntypedOrigin::Propagated;
    let mut joined_environment: Option<Environment> = None;
    let mut resolved = false;

    for candidate in candidates {
        let mut member_environment = initial_environment.clone();
        let result = transfer_receiver_call_with_substitution(
            analyzer,
            input,
            &candidate,
            substitution_receiver,
            arguments,
            values,
            &mut member_environment,
            hash_shape,
        )?;
        if result.missing_method {
            continue;
        }
        resolved = true;
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
    }

    if !resolved {
        return Ok(None);
    }
    if let Some(joined_environment) = joined_environment {
        *environment = joined_environment;
    }
    Ok(Some(ReceiverTransfer {
        type_: result_type,
        block_result,
        untyped_origin,
        missing_method: false,
    }))
}

fn structural_collection_receiver(receiver: &Type) -> Option<Type> {
    let Type::Named(name, arguments) = receiver else {
        return None;
    };
    match (
        name_matches(name, "Array"),
        name_matches(name, "Hash"),
        arguments.as_slice(),
    ) {
        (true, false, []) => Some(Type::Array(Box::new(Type::Any))),
        (true, false, [element]) => Some(Type::Array(Box::new(element.clone()))),
        (false, true, []) => Some(Type::Hash(Box::new(Type::Any), Box::new(Type::Any))),
        (false, true, [key, value]) => {
            Some(Type::Hash(Box::new(key.clone()), Box::new(value.clone())))
        }
        _ => None,
    }
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
