//! Receiver dispatch and call termination semantics.
//!
//! Argument materialization and signature invocation live in `calls.rs` and
//! `signature_calls.rs`. This layer owns the receiver-side method selection
//! rules that sit between those two concerns.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_polymorphic_receiver_call<'a, 'node>(
        &mut self,
        node: &Node<'node>,
        receiver_node: Option<&Node<'node>>,
        receiver_type: &Type,
        name: &str,
        arguments: &CallArguments<'node>,
        block: Option<&Node<'node>>,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> (Type, UntypedOrigin) {
        if let Type::Union(members) = receiver_type {
            if matches!(name, "call" | "[]")
                && members.iter().all(|member| {
                    member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
                })
            {
                let type_ = self.eval_method_call(receiver_type, name, site, environment);
                return (type_, UntypedOrigin::InferredMethod);
            }
            let mut result = Type::Never;
            let mut fallback_origin = UntypedOrigin::FallbackCall;
            for member in members {
                let (member_type, member_origin) = self.eval_polymorphic_receiver_call(
                    node,
                    receiver_node,
                    member,
                    name,
                    arguments,
                    block,
                    site,
                    environment,
                );
                if member_type.contains_any() {
                    fallback_origin = member_origin;
                }
                result = result.join(&member_type);
            }
            return (
                if result.is_never() { Type::Any } else { result },
                fallback_origin,
            );
        }

        // `T.class_of(Foo)[T.all(Foo, M)]` is still a class object whose
        // singleton methods come from Foo. Look up those methods through the
        // intersected instance members while retaining the full receiver for
        // `T.attached_class` substitution.
        if let Type::Named(class, type_arguments) = receiver_type {
            if (name_matches(class, "Class") || name_matches(class, "Module"))
                && type_arguments
                    .first()
                    .is_some_and(|argument| matches!(argument, Type::Intersection(_)))
            {
                if let Some(Type::Intersection(members)) = type_arguments.first() {
                    for member in members {
                        let candidate = Type::Named(class.clone(), vec![member.clone()]);
                        let Some(key) =
                            self.receiver_method_key(receiver_node, &candidate, name, environment)
                        else {
                            continue;
                        };
                        if let Some((type_, declared)) = self.eval_resolved_receiver_call(
                            node,
                            name,
                            receiver_node,
                            &key,
                            receiver_type,
                            arguments,
                            block,
                            environment,
                        ) {
                            let origin = if declared {
                                UntypedOrigin::DeclaredSignature
                            } else {
                                UntypedOrigin::InferredMethod
                            };
                            return (type_, origin);
                        }
                    }
                }
            }
        }

        if let Type::Intersection(members) = receiver_type {
            for member in members {
                let Some(key) = self.receiver_method_key(receiver_node, member, name, environment)
                else {
                    continue;
                };
                if let Some((type_, declared)) = self.eval_resolved_receiver_call(
                    node,
                    name,
                    receiver_node,
                    &key,
                    member,
                    arguments,
                    block,
                    environment,
                ) {
                    let origin = if declared {
                        UntypedOrigin::DeclaredSignature
                    } else {
                        UntypedOrigin::InferredMethod
                    };
                    return (type_, origin);
                }
            }
            let type_ = self.eval_method_call(receiver_type, name, site, environment);
            let origin = if receiver_type.contains_any() {
                UntypedOrigin::Propagated
            } else {
                UntypedOrigin::FallbackCall
            };
            return (type_, origin);
        }

        if let Some(key) = self.receiver_method_key(receiver_node, receiver_type, name, environment)
        {
            if let Some((type_, declared)) = self.eval_resolved_receiver_call(
                node,
                name,
                receiver_node,
                &key,
                receiver_type,
                arguments,
                block,
                environment,
            ) {
                let origin = if declared {
                    UntypedOrigin::DeclaredSignature
                } else {
                    UntypedOrigin::InferredMethod
                };
                return (type_, origin);
            }
        }

        let type_ = self.eval_method_call(receiver_type, name, site, environment);
        let origin = if receiver_type.contains_any() {
            UntypedOrigin::Propagated
        } else {
            UntypedOrigin::FallbackCall
        };
        (type_, origin)
    }

    pub(super) fn eval_resolved_receiver_call<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        receiver_node: Option<&Node<'node>>,
        key: &MethodKey,
        receiver_type: &Type,
        arguments: &CallArguments<'node>,
        block: Option<&Node<'node>>,
        environment: &mut Environment,
    ) -> Option<(Type, bool)> {
        let resolved_owner = self
            .resolve_method_key(key)
            .and_then(|resolved| resolved.owner);
        if self
            .resolve_method_key(key)
            .and_then(|resolved| self.declarations.methods.get(&resolved))
            .is_some_and(|state| state.visibility == Visibility::Private)
            && receiver_node.is_some()
            && !self.private_call_allowed(key, environment)
        {
            self.error(
                node,
                format!("Non-private call to private method `{name}` on `{receiver_type}`"),
            );
            return Some((Type::Any, true));
        }
        if let Some(type_) =
            self.eval_tsort_method(receiver_type, name, environment, resolved_owner.as_deref())
        {
            return Some((type_, false));
        }
        if matches!(receiver_type, Type::Tuple(_))
            && matches!(name, "first" | "last")
            && arguments.argument_types.is_empty()
        {
            // A fixed tuple is more precise than the generic Array RBI.  In
            // particular, `const_source_location(...).first` is known to be
            // the tuple's String component, not an unresolved Array::Elem.
            return Some((
                self.eval_method_call(
                    receiver_type,
                    name,
                    &CallSite {
                        argument_nodes: &arguments.argument_nodes,
                        argument_types: &arguments.argument_types,
                        block,
                    },
                    environment,
                ),
                false,
            ));
        }
        self.record_method_dependency(key, environment);
        let inferred_accessor = self
            .resolve_method_key(key)
            .filter(|resolved| {
                self.declarations
                    .methods
                    .get(resolved)
                    .is_some_and(|state| !state.explicit)
            })
            .and_then(|resolved| {
                self.declarations
                    .accessors
                    .get(&resolved)
                    .copied()
                    .map(|accessor| (resolved, accessor))
            });
        if let Some((accessor_key, accessor)) = inferred_accessor {
            return Some((
                self.eval_accessor_call(
                    &accessor_key,
                    accessor,
                    &arguments.argument_types,
                    environment,
                ),
                false,
            ));
        }

        let signature = self.observe_call(key, arguments, block.is_some())?;
        let signature = self.widen_overridable_noreturn(key, signature);
        let declared = self
            .resolve_method_key(key)
            .and_then(|resolved| self.declarations.methods.get(&resolved))
            .is_some_and(|state| state.explicit);
        let block_return_type = self.observe_block_call(
            key,
            block,
            &signature,
            arguments,
            Some(receiver_type),
            environment,
        );
        let type_ = if let Some(type_) =
            self.eval_node_helpers_method(receiver_type, name, &arguments.argument_types)
        {
            type_
        } else {
            self.invoke_signature(
                node,
                name,
                &signature,
                arguments,
                Some(receiver_type),
                block_return_type.as_ref(),
            )
        };
        let type_ = self.widen_recursive_call_return(key, type_, environment);
        Some((type_, declared))
    }

    /// An inferred method whose only observed path raises is provisionally
    /// represented as `T.noreturn`. That is useful for local helper methods,
    /// but it is not sound for an ordinary Ruby instance method: subclasses
    /// can override it and return normally. Keep the precise return types of
    /// known overrides when available, and otherwise use the static top type
    /// rather than leaking `T.noreturn` into the base implementation.
    pub(super) fn widen_overridable_noreturn(
        &self,
        key: &MethodKey,
        mut signature: MethodSig,
    ) -> MethodSig {
        let Some(resolved) = self.resolve_method_key(key) else {
            return signature;
        };
        let Some(state) = self.declarations.methods.get(&resolved) else {
            return signature;
        };
        if !state.explicit && state.return_type.is_none() {
            // Inferred methods use `Never` as the worklist's provisional
            // bottom. That is not evidence that the call terminates: the
            // method may simply have not been evaluated yet (often because
            // it is declared after a DSL callback that calls it). Keep the
            // callback's normal path alive until convergence supplies the
            // actual summary.
            signature.return_type = Type::Any;
            return signature;
        }
        if state.explicit
            || !state.return_terminates
            || !state.return_type.as_ref().is_some_and(Type::is_never)
        {
            return signature;
        }
        let Some(owner) = resolved.owner.as_deref() else {
            return signature;
        };

        let mut override_type = Type::Never;
        let mut found_override = false;
        for (candidate, candidate_state) in &self.declarations.methods {
            if candidate.singleton != resolved.singleton
                || candidate.name != resolved.name
                || candidate.owner.as_deref() == Some(owner)
            {
                continue;
            }
            let Some(candidate_owner) = candidate.owner.as_deref() else {
                continue;
            };
            if !self.nominal_subtype_names(nominal_name(candidate_owner), nominal_name(owner)) {
                continue;
            }
            found_override = true;
            let Some(return_type) = candidate_state.return_type.as_ref() else {
                signature.return_type = Type::union([Type::Nil, Type::Object]);
                return signature;
            };
            if return_type.is_any() {
                signature.return_type = Type::union([Type::Nil, Type::Object]);
                return signature;
            }
            if !return_type.is_never() {
                override_type = override_type.join(return_type);
            }
        }

        if found_override {
            signature.return_type = if override_type.is_never() {
                Type::union([Type::Nil, Type::Object])
            } else {
                override_type
            };
        }
        signature
    }

    pub(super) fn private_call_allowed(&self, key: &MethodKey, environment: &Environment) -> bool {
        let Some(current) = environment.method_key.as_ref() else {
            return false;
        };
        let Some(current_owner) = current.owner.as_deref() else {
            return false;
        };
        let Some(resolved_owner) = self
            .resolve_method_key(key)
            .and_then(|resolved| resolved.owner)
        else {
            return false;
        };
        current_owner == resolved_owner
            || (!current.singleton && self.nominal_subtype(current_owner, &resolved_owner))
            || (current.singleton
                && key.singleton
                && self.nominal_subtype(current_owner, &resolved_owner))
    }

    pub(super) fn call_terminates<'node>(
        &self,
        call: &HirCallView<'node>,
        environment: &Environment,
        receiver_type: &Type,
        type_: &Type,
    ) -> bool {
        let name = call.name();
        if call.receiver().is_none()
            && matches!(name.as_str(), "raise" | "fail" | "abort" | "exit" | "exit!")
        {
            return true;
        }
        if call.receiver().as_ref().is_some_and(|receiver| {
            self.constant_reference_name(receiver)
                .is_some_and(|name| name.trim_start_matches("::") == "T")
        }) {
            return matches!(name.as_str(), "noreturn" | "absurd");
        }
        if !type_.is_never() {
            return false;
        }
        let key = if let Some(receiver) = call.receiver() {
            let Some(key) =
                self.receiver_method_key(Some(&receiver), receiver_type, &name, environment)
            else {
                return false;
            };
            key
        } else {
            self.implicit_method_key(&name, environment)
        };
        let Some(key) = self.resolve_method_key(&key) else {
            return false;
        };
        self.declarations.methods.get(&key).is_some_and(|state| {
            state.return_terminates && state.return_type.as_ref().is_some_and(Type::is_never)
        })
    }

    pub(super) fn super_terminates(&self, environment: &Environment) -> bool {
        let Some(current) = environment.method_key.as_ref() else {
            return false;
        };
        let Some(target) = self.super_method_key(current) else {
            return false;
        };
        self.declarations.methods.get(&target).is_some_and(|state| {
            state.return_terminates && state.return_type.as_ref().is_some_and(Type::is_never)
        })
    }
}
