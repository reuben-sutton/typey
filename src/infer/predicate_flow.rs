use super::method_types::proc_arity_narrowing;
use super::{
    ivar_refinement_key, name_matches, Analyzer, CallSite, Environment, Eval, Flow, FlowKind,
    PredicateAlias,
};
use crate::prism;
use crate::signature;
use crate::types::Type;
use ruby_prism::{CallNode, Node};

impl<'src> Analyzer<'src> {
    pub(super) fn predicate_reachability<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
        predicate_type: &Type,
    ) -> (bool, bool) {
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                return self.predicate_reachability(&body, environment, predicate_type);
            }
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            if environment.is_inferred(&name) {
                return (true, true);
            }
            if let Some(truthy) = environment.known_truthiness(&name) {
                return (truthy, !truthy);
            }
            if let Some(alias) = environment.predicate_alias(&name) {
                let source_type = environment.get(&alias.source);
                let (then_reachable, else_reachable) = if let Some(expected) = &alias.expected {
                    (
                        !source_type.meet(expected).is_never(),
                        !source_type.without(expected).is_never(),
                    )
                } else {
                    (
                        !source_type.truthy_part().is_never(),
                        !source_type.falsy_part().is_never(),
                    )
                };
                return if alias.negated {
                    (else_reachable, then_reachable)
                } else {
                    (then_reachable, else_reachable)
                };
            }
            let type_ = environment.get(&name);
            return (
                !type_.truthy_part().is_never(),
                !type_.falsy_part().is_never(),
            );
        }
        if let Some(and) = node.as_and_node() {
            let left = self.predicate_reachability(
                &and.left(),
                environment,
                &self.predicate_type_for_node(&and.left(), environment, predicate_type),
            );
            let right = self.predicate_reachability(
                &and.right(),
                environment,
                &self.predicate_type_for_node(&and.right(), environment, predicate_type),
            );
            return (left.0 && right.0, left.1 || (left.0 && right.1));
        }
        if let Some(or) = node.as_or_node() {
            let left = self.predicate_reachability(
                &or.left(),
                environment,
                &self.predicate_type_for_node(&or.left(), environment, predicate_type),
            );
            let right = self.predicate_reachability(
                &or.right(),
                environment,
                &self.predicate_type_for_node(&or.right(), environment, predicate_type),
            );
            return (left.0 || (left.1 && right.0), left.1 && right.1);
        }
        if let Some(call) = node.as_call_node() {
            let name = prism::constant_name(call.name());
            if call.receiver().is_some_and(|receiver| {
                receiver.as_local_variable_read_node().is_some_and(|local| {
                    environment.is_inferred(&prism::constant_name(local.name()))
                })
            }) {
                return (true, true);
            }
            if name == "==="
                && call.arguments().is_some_and(|arguments| {
                    arguments.arguments().into_iter().any(|argument| {
                        argument.as_local_variable_read_node().is_some_and(|local| {
                            environment.is_inferred(&prism::constant_name(local.name()))
                        })
                    })
                })
            {
                return (true, true);
            }
            if name == "!" {
                if let Some(receiver) = call.receiver() {
                    let can_refine_receiver = receiver.as_local_variable_read_node().is_some()
                        || receiver.as_parentheses_node().is_some()
                        || receiver
                            .as_call_node()
                            .is_some_and(|call| prism::constant_name(call.name()) == "!");
                    if can_refine_receiver {
                        let (then_reachable, else_reachable) =
                            self.predicate_reachability(&receiver, environment, predicate_type);
                        return (else_reachable, then_reachable);
                    }
                    if let Some(receiver_type) = self.recorded_node_type(&receiver) {
                        return (
                            !receiver_type.falsy_part().is_never(),
                            !receiver_type.truthy_part().is_never(),
                        );
                    }
                }
            } else if name == "block_given?" && call.receiver().is_none() {
                let required = environment
                    .method_key
                    .as_ref()
                    .and_then(|key| self.declarations.methods.get(key))
                    .is_some_and(|state| state.explicit && state.block.is_some());
                if required {
                    return (true, false);
                }
            } else if name == "nil?" {
                if let Some(receiver) = call.receiver() {
                    if let Some(receiver_type) = self.recorded_node_type(&receiver) {
                        return (
                            !receiver_type.meet(&Type::Nil).is_never(),
                            !receiver_type.without(&Type::Nil).is_never(),
                        );
                    }
                }
            } else if matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?") {
                if let (Some(receiver), Some(arguments)) = (
                    call.receiver(),
                    call.arguments()
                        .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>()),
                ) {
                    if let Some(local) = receiver.as_local_variable_read_node() {
                        if let Some(argument) = arguments.first() {
                            let current = environment.get(&prism::constant_name(local.name()));
                            let expected = self.predicate_expected_type(argument, environment);
                            let truthy = self.meet_predicate_type(&current, &expected);
                            let falsy = current.without(&expected);
                            return (!truthy.is_never(), !falsy.is_never());
                        }
                    }
                }
            }
        }
        (
            !predicate_type.truthy_part().is_never(),
            !predicate_type.falsy_part().is_never(),
        )
    }

    pub(super) fn predicate_type_for_node<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
        fallback: &Type,
    ) -> Type {
        self.recorded_node_type(node).unwrap_or_else(|| {
            node.as_local_variable_read_node()
                .map(|local| environment.get(&prism::constant_name(local.name())))
                .unwrap_or_else(|| fallback.clone())
        })
    }

    pub(super) fn predicate_is_precise<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> bool {
        if let Some(parentheses) = node.as_parentheses_node() {
            return parentheses
                .body()
                .is_some_and(|body| self.predicate_is_precise(&body, environment));
        }
        if node.as_statements_node().is_some_and(|statements| {
            statements
                .body()
                .into_iter()
                .last()
                .is_some_and(|last| self.predicate_is_precise(&last, environment))
        }) {
            return true;
        }
        if node.as_true_node().is_some()
            || node.as_false_node().is_some()
            || node.as_nil_node().is_some()
            || node.as_integer_node().is_some()
            || node.as_string_node().is_some()
        {
            return true;
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            return !environment.is_inferred(&name)
                && (environment.known_truthiness(&name).is_some()
                    || !environment.get(&name).is_any());
        }
        if let Some(and) = node.as_and_node() {
            return self.predicate_is_precise(&and.left(), environment)
                && self.predicate_is_precise(&and.right(), environment);
        }
        if let Some(or) = node.as_or_node() {
            return self.predicate_is_precise(&or.left(), environment)
                && self.predicate_is_precise(&or.right(), environment);
        }
        let Some(call) = node.as_call_node() else {
            return false;
        };
        let name = prism::constant_name(call.name());
        if call.receiver().is_some_and(|receiver| {
            receiver
                .as_local_variable_read_node()
                .is_some_and(|local| environment.is_inferred(&prism::constant_name(local.name())))
        }) {
            return false;
        }
        if name == "==="
            && call.arguments().is_some_and(|arguments| {
                arguments.arguments().into_iter().any(|argument| {
                    argument.as_local_variable_read_node().is_some_and(|local| {
                        environment.is_inferred(&prism::constant_name(local.name()))
                    })
                })
            })
        {
            return false;
        }
        if name == "!" {
            return call
                .receiver()
                .is_some_and(|receiver| self.predicate_is_precise(&receiver, environment));
        }
        if name == "block_given?" && call.receiver().is_none() {
            // Sorbet uses a required callable block in the surrounding
            // signature to typecheck the false arm as unreachable, but does
            // not emit an unreachable-code diagnostic for this Ruby idiom.
            return false;
        }
        if matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?")
            && call.receiver().is_some()
            && call
                .arguments()
                .is_some_and(|arguments| !arguments.arguments().is_empty())
        {
            return call.receiver().is_some_and(|receiver| {
                receiver.as_local_variable_read_node().is_some_and(|local| {
                    !environment
                        .get(&prism::constant_name(local.name()))
                        .is_any()
                })
            });
        }
        if let Some(receiver) = call.receiver() {
            let receiver_type = self.recorded_node_type(&receiver).or_else(|| {
                receiver
                    .as_local_variable_read_node()
                    .map(|local| environment.get(&prism::constant_name(local.name())))
            });
            if let Some(receiver_type) = receiver_type {
                if let Some(key) =
                    self.receiver_method_key(Some(&receiver), &receiver_type, &name, environment)
                {
                    return self
                        .resolve_method_key(&key)
                        .and_then(|resolved| self.declarations.methods.get(&resolved))
                        .is_some_and(|state| state.explicit);
                }
            }
        } else {
            let key = self.implicit_method_key(&name, environment);
            return self
                .resolve_method_key(&key)
                .and_then(|resolved| self.declarations.methods.get(&resolved))
                .is_some_and(|state| state.explicit);
        }
        false
    }

    pub(super) fn recorded_node_type(&self, node: &Node<'_>) -> Option<Type> {
        let (start, end) = prism::span(node);
        self.types
            .iter()
            .rev()
            .find(|inferred| inferred.start == start && inferred.end == end)
            .map(|inferred| inferred.type_.clone())
    }

    pub(super) fn should_report_unreachable_branch(&self, node: &Node<'_>) -> bool {
        let start = prism::span(node).0;
        self.source[..start]
            .iter()
            .rev()
            .find(|byte| !byte.is_ascii_whitespace())
            .is_none_or(|byte| *byte != b'=')
    }

    pub(super) fn eval_alternative<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if let Some(if_node) = node.as_if_node() {
            return self.eval_if_dispatch(node, &if_node, environment);
        }
        if let Some(unless) = node.as_unless_node() {
            return self.eval_unless(node, &unless, environment);
        }
        if let Some(else_clause) = node.as_else_node() {
            if let Some(statements) = else_clause.statements() {
                return self.eval_statements(&statements, environment);
            }
        }
        self.eval_node(node, environment)
    }

    pub(super) fn join_flow_environments(
        &self,
        left: &Environment,
        left_flow: Flow,
        right: &Environment,
        right_flow: Flow,
    ) -> Environment {
        match (
            left_flow.contains(FlowKind::Normal),
            right_flow.contains(FlowKind::Normal),
        ) {
            (true, false) => left.clone(),
            (false, true) => right.clone(),
            _ => left.join(right),
        }
    }

    /// Refine a local using the lattice's greatest-lower-bound operation.
    /// This is intentionally a small, explicit refinement hook: adding a new
    /// predicate should not require changing the rest of inference.
    pub(super) fn narrow_from_predicate<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                self.narrow_from_predicate(&body, environment, truthy);
            }
            return;
        }
        if let Some(statements) = node.as_statements_node() {
            let body = statements.body();
            if let Some(last) = (&body).into_iter().last() {
                self.narrow_from_predicate(&last, environment, truthy);
            }
            return;
        }
        if let Some(and) = node.as_and_node() {
            if truthy {
                let left = and.left();
                self.narrow_from_predicate(&left, environment, true);
                let right = and.right();
                self.narrow_from_predicate(&right, environment, true);
            }
            return;
        }
        if let Some(or) = node.as_or_node() {
            if truthy {
                let left = self.positive_type_test(&or.left(), environment);
                let right = self.positive_type_test(&or.right(), environment);
                if let (Some((left_name, left_type)), Some((right_name, right_type))) =
                    (left, right)
                {
                    if left_name == right_name {
                        let expected = left_type.join(&right_type);
                        if left_name == "<self>" {
                            let current = environment.self_type.clone();
                            environment.self_type = self.meet_predicate_type(&current, &expected);
                        } else {
                            let current = environment.get(&left_name);
                            environment
                                .bind(left_name, self.meet_predicate_type(&current, &expected));
                        }
                    }
                }
            } else {
                let left = or.left();
                self.narrow_from_predicate(&left, environment, false);
                let right = or.right();
                self.narrow_from_predicate(&right, environment, false);
            }
            return;
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            if environment.is_inferred(&name) {
                return;
            }
            if let Some(alias) = environment.predicate_alias(&name).cloned() {
                let source_current = environment.get(&alias.source);
                let source_truthy = if alias.negated { !truthy } else { truthy };
                let source_narrowed = if let Some(expected) = alias.expected.as_ref() {
                    if source_truthy {
                        source_current.meet(&expected)
                    } else {
                        source_current.without(&expected)
                    }
                } else if source_truthy {
                    source_current.truthy_part()
                } else {
                    source_current.falsy_part()
                };
                environment.bind(alias.source.clone(), source_current.meet(&source_narrowed));
                if alias.expected.is_none() {
                    environment.set_known_truthiness(alias.source, source_truthy);
                }
            }
            let current = environment.get(&name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(name.clone(), current.meet(&narrowed));
            environment.set_known_truthiness(name, truthy);
            return;
        }
        if let Some(write) = node.as_local_variable_write_node() {
            let name = prism::constant_name(write.name());
            let current = environment.get(&name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(name.clone(), current.meet(&narrowed));
            environment.set_known_truthiness(name, truthy);
            return;
        }
        if let Some(instance_variable) = node.as_instance_variable_read_node() {
            let name = prism::constant_name(instance_variable.name());
            let current = self.ivar_type(environment, &name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(ivar_refinement_key(&name), current.meet(&narrowed));
            return;
        }
        if let Some(call) = node.as_call_node() {
            let name = prism::constant_name(call.name());
            let receiver = call.receiver();
            let arguments = call
                .arguments()
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            if name == "!" {
                if let Some(receiver) = receiver {
                    self.narrow_from_predicate(&receiver, environment, !truthy);
                }
                return;
            }
            if truthy
                && name == "string?"
                && call.receiver().as_ref().is_some_and(|receiver| {
                    self.constant_reference_name(receiver)
                        .is_some_and(|name| self.nominal_names_match(&name, "NodeHelpers"))
                })
            {
                if let Some(argument) = arguments.first() {
                    if let Some(local) = argument.as_local_variable_read_node() {
                        let name = prism::constant_name(local.name());
                        let current = environment.get(&name);
                        environment.bind(
                            name,
                            Type::intersection([current, Type::named("AST::StringNode")]),
                        );
                    }
                }
            }
            if let Some(receiver) = receiver {
                if name == "===" && arguments.len() == 1 {
                    if let Some(local) = arguments[0].as_local_variable_read_node() {
                        let local_name = prism::constant_name(local.name());
                        let class_type = self.node_type(&receiver, environment);
                        let expected = Self::class_object_value_type(&class_type)
                            .unwrap_or_else(|| class_type.clone());
                        let current = environment.get(&local_name);
                        let narrowed = if truthy {
                            self.meet_predicate_type(&current, &expected)
                        } else {
                            current.without(&expected)
                        };
                        environment.bind(local_name, narrowed);
                        return;
                    }
                    if let Some(instance_variable) = arguments[0].as_instance_variable_read_node() {
                        let class_type = self.node_type(&receiver, environment);
                        let expected = Self::class_object_value_type(&class_type)
                            .unwrap_or_else(|| class_type.clone());
                        let instance_variable_name = prism::constant_name(instance_variable.name());
                        let current = self.ivar_type(environment, &instance_variable_name);
                        let narrowed = if truthy {
                            self.meet_predicate_type(&current, &expected)
                        } else {
                            current.without(&expected)
                        };
                        environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                        return;
                    }
                }
                if truthy && name == "==" && arguments.len() == 1 {
                    if let Some(arity_call) = receiver.as_call_node() {
                        if prism::constant_name(arity_call.name()) == "arity"
                            && arity_call.arguments().is_none()
                        {
                            if let Some(block_local) = arity_call
                                .receiver()
                                .and_then(|receiver| receiver.as_local_variable_read_node())
                            {
                                if let Some(integer) = arguments[0].as_integer_node() {
                                    let value: Result<i32, _> = integer.value().try_into();
                                    if let Ok(value) = value {
                                        if let Ok(arity) = usize::try_from(value) {
                                            let block_name =
                                                prism::constant_name(block_local.name());
                                            if !environment.is_inferred(&block_name) {
                                                let current = environment.get(&block_name);
                                                if let Some(narrowed) =
                                                    proc_arity_narrowing(&current, arity)
                                                {
                                                    environment.bind(block_name, narrowed);
                                                    return;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if name == "empty?" {
                    if let Some(local) = receiver.as_local_variable_read_node() {
                        let local_name = prism::constant_name(local.name());
                        if matches!(
                            environment.get(&local_name),
                            Type::Array(_) | Type::Tuple(_)
                        ) {
                            environment.set_known_nonempty_array(&local_name, !truthy);
                        }
                        return;
                    }
                }
                if let Some(local) = receiver.as_local_variable_read_node() {
                    let local_name = prism::constant_name(local.name());
                    if environment.is_inferred(&local_name) {
                        return;
                    }
                    let current = environment.get(&local_name);
                    if matches!(name.as_str(), "<" | "<=") && arguments.len() == 1 {
                        let expected = self.resolve_type_names(
                            &self.predicate_expected_type(&arguments[0], environment),
                            None,
                        );
                        let narrowed =
                            self.class_object_subclass_narrowing(&current, &expected, truthy);
                        environment.bind(local_name, narrowed);
                        return;
                    }
                    if let Some(narrowed) = self.equality_predicate_narrowing(
                        &name,
                        &current,
                        &arguments,
                        truthy,
                        environment,
                    ) {
                        environment.bind(local_name, narrowed);
                        return;
                    }
                    let safe_navigation_non_nil = call.is_safe_navigation()
                        && (truthy
                            || self.safe_navigation_method_returns_non_nil(
                                &receiver,
                                &current,
                                &name,
                                &arguments,
                                environment,
                            ));
                    let narrowed = match name.as_str() {
                        "nil?" => {
                            if truthy {
                                current.meet(&Type::Nil)
                            } else {
                                current.without(&Type::Nil)
                            }
                        }
                        "is_a?" | "kind_of?" | "instance_of?" if !arguments.is_empty() => {
                            let expected = self.predicate_expected_type(&arguments[0], environment);
                            if truthy {
                                self.meet_predicate_type(&current, &expected)
                            } else {
                                current.without(&expected)
                            }
                        }
                        _ if safe_navigation_non_nil => current.without(&Type::Nil),
                        _ => return,
                    };
                    environment.bind(local_name, narrowed);
                } else if let Some(instance_variable) = receiver.as_instance_variable_read_node() {
                    let instance_variable_name = prism::constant_name(instance_variable.name());
                    let current = self.ivar_type(environment, &instance_variable_name);
                    if truthy && name == "===" && arguments.len() == 1 {
                        let class_type = self.node_type(&receiver, environment);
                        let expected = Self::class_object_value_type(&class_type)
                            .unwrap_or_else(|| class_type.clone());
                        environment.bind(
                            ivar_refinement_key(&instance_variable_name),
                            self.meet_predicate_type(&current, &expected),
                        );
                        return;
                    }
                    if let Some(narrowed) = self.equality_predicate_narrowing(
                        &name,
                        &current,
                        &arguments,
                        truthy,
                        environment,
                    ) {
                        environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                        return;
                    }
                    let safe_navigation_non_nil = call.is_safe_navigation()
                        && (truthy
                            || self.safe_navigation_method_returns_non_nil(
                                &receiver,
                                &current,
                                &name,
                                &arguments,
                                environment,
                            ));
                    let narrowed = match name.as_str() {
                        "nil?" => {
                            if truthy {
                                current.meet(&Type::Nil)
                            } else {
                                current.without(&Type::Nil)
                            }
                        }
                        "is_a?" | "kind_of?" | "instance_of?" if !arguments.is_empty() => {
                            let expected = self.predicate_expected_type(&arguments[0], environment);
                            if truthy {
                                self.meet_predicate_type(&current, &expected)
                            } else {
                                current.without(&expected)
                            }
                        }
                        _ if safe_navigation_non_nil => current.without(&Type::Nil),
                        _ => return,
                    };
                    environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                }
            } else if matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?")
                && !arguments.is_empty()
            {
                let current = environment.self_type.clone();
                let expected = self.predicate_expected_type(&arguments[0], environment);
                environment.self_type = if truthy {
                    self.meet_predicate_type(&current, &expected)
                } else {
                    current.without(&expected)
                };
            }
        }
    }

    pub(super) fn positive_type_test<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Option<(String, Type)> {
        let call = node.as_call_node()?;
        let name = prism::constant_name(call.name());
        if !matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?") {
            return None;
        }
        let argument = call
            .arguments()
            .and_then(|arguments| arguments.arguments().into_iter().next())?;
        let local = match call.receiver() {
            None => "<self>".to_owned(),
            Some(receiver) => {
                let local = receiver.as_local_variable_read_node()?;
                let name = prism::constant_name(local.name());
                if environment.is_inferred(&name) {
                    return None;
                }
                name
            }
        };
        Some((local, self.predicate_expected_type(&argument, environment)))
    }

    pub(super) fn meet_predicate_type(&self, current: &Type, expected: &Type) -> Type {
        if let Type::Union(members) = current {
            return Type::union(
                members
                    .iter()
                    .map(|member| self.meet_predicate_type(member, expected)),
            );
        }
        if self.is_assignable(expected, current) {
            expected.clone()
        } else if self.is_assignable(current, expected) {
            // The current type may be a more precise structural form of the
            // predicate's nominal class. For example, a fixed tuple is an
            // Array, but intersecting it with the bare `Array` nominal would
            // discard its element positions and route `[]` through the
            // unparameterized fallback model.
            current.clone()
        } else if Self::definitely_disjoint_class_types(self, current, expected) {
            Type::Never
        } else {
            current.meet(expected)
        }
    }

    pub(super) fn class_object_subclass_narrowing(
        &self,
        current: &Type,
        expected: &Type,
        truthy: bool,
    ) -> Type {
        if !truthy {
            return current.clone();
        }
        match current {
            Type::Union(members) => Type::union(members.iter().filter_map(|member| {
                let narrowed = self.class_object_subclass_narrowing(member, expected, true);
                (!narrowed.is_never()).then_some(narrowed)
            })),
            Type::Intersection(members) => {
                let mut narrowed = Vec::new();
                for member in members {
                    let next = if Self::is_class_or_module_object(member) {
                        self.class_object_subclass_narrowing(member, expected, true)
                    } else {
                        member.clone()
                    };
                    if next.is_never() {
                        return Type::Never;
                    }
                    narrowed.push(next);
                }
                Type::intersection(narrowed)
            }
            Type::Named(name, arguments)
                if name_matches(name, "Class") || name_matches(name, "Module") =>
            {
                if arguments.is_empty() {
                    return Type::Named(name.clone(), vec![expected.clone()]);
                }
                let instance = arguments.first().cloned().unwrap_or(Type::Any);
                if let Type::Union(members) = &instance {
                    let narrowed = Type::union(members.iter().filter_map(|member| {
                        if self.is_assignable(member, expected) {
                            Some(member.clone())
                        } else if Self::definitely_disjoint_class_types(self, member, expected) {
                            None
                        } else {
                            let member = member.meet(expected);
                            (!member.is_never()).then_some(member)
                        }
                    }));
                    return if narrowed.is_never() {
                        Type::Never
                    } else {
                        Type::Named(name.clone(), vec![narrowed])
                    };
                }
                if !instance.is_any() && self.is_assignable(&instance, expected) {
                    return current.clone();
                }
                if Self::definitely_disjoint_class_types(self, &instance, expected) {
                    return Type::Never;
                }
                let instance = instance.meet(expected);
                if instance.is_never() {
                    Type::Never
                } else {
                    Type::Named(name.clone(), vec![instance])
                }
            }
            _ => current.clone(),
        }
    }

    pub(super) fn is_class_or_module_object(type_: &Type) -> bool {
        matches!(
            type_,
            Type::Named(name, _) if name_matches(name, "Class") || name_matches(name, "Module")
        )
    }

    pub(super) fn definitely_disjoint_class_types(&self, actual: &Type, expected: &Type) -> bool {
        let Some(actual_name) = Self::class_instance_name(actual) else {
            return false;
        };
        let Some(expected_name) = Self::class_instance_name(expected) else {
            return false;
        };
        if !self.known_nominal_name(&actual_name) || !self.known_nominal_name(&expected_name) {
            return false;
        }
        // A Ruby class can include a module (and a module can be mixed into
        // another module), so two nominal names are not enough to prove that
        // this refinement is impossible. Sorbet keeps the class-object
        // intersection in cases such as `klass < Exportable`.
        if self
            .declarations
            .classes
            .get(&actual_name)
            .is_some_and(|info| info.is_module)
            || self
                .declarations
                .classes
                .get(&expected_name)
                .is_some_and(|info| info.is_module)
        {
            return false;
        }
        !self.nominal_subtype(&actual_name, &expected_name)
            && !self.nominal_subtype(&expected_name, &actual_name)
    }

    pub(super) fn class_instance_name(type_: &Type) -> Option<String> {
        match type_ {
            Type::Named(name, _) => Some(name.clone()),
            Type::Integer => Some("Integer".to_owned()),
            Type::Float => Some("Float".to_owned()),
            Type::String => Some("String".to_owned()),
            Type::Symbol => Some("Symbol".to_owned()),
            Type::Object => Some("Object".to_owned()),
            _ => None,
        }
    }

    pub(super) fn known_nominal_name(&self, name: &str) -> bool {
        self.declarations.classes.contains_key(name)
            || matches!(name, "ActiveSupport::Inflector")
            || matches!(
                name.rsplit_once("::").map_or(name, |(_, tail)| tail),
                "BasicObject"
                    | "Object"
                    | "Kernel"
                    | "Numeric"
                    | "Integer"
                    | "Float"
                    | "Rational"
                    | "Complex"
                    | "String"
                    | "Symbol"
                    | "Array"
                    | "Hash"
                    | "Range"
                    | "Regexp"
                    | "MatchData"
                    | "Encoding"
                    | "Time"
                    | "Date"
                    | "DateTime"
                    | "Class"
                    | "Module"
                    | "Proc"
                    | "Binding"
                    | "Method"
                    | "UnboundMethod"
                    | "Enumerator"
                    | "Struct"
                    | "Thread"
                    | "Mutex"
                    | "Ractor"
                    | "Fiber"
                    | "IO"
                    | "File"
                    | "Dir"
                    | "ENV"
                    | "ARGF"
                    | "Set"
                    | "Random"
                    | "SecureRandom"
                    | "OptionParser"
                    | "JSON"
                    | "Psych"
                    | "YAML"
                    | "ActiveSupport"
                    | "ActiveSupport::Inflector"
                    | "Exception"
                    | "StandardError"
                    | "RuntimeError"
                    | "ArgumentError"
                    | "TypeError"
                    | "NameError"
                    | "NoMethodError"
                    | "IOError"
                    | "SystemCallError"
                    | "NilClass"
                    | "TrueClass"
                    | "FalseClass"
            )
    }

    pub(super) fn predicate_alias_for_value<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Option<PredicateAlias> {
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            return environment
                .predicate_alias(&name)
                .cloned()
                .or(Some(PredicateAlias {
                    source: name,
                    negated: false,
                    expected: None,
                }));
        }
        let call = node.as_call_node()?;
        let name = prism::constant_name(call.name());
        if name == "!" {
            let receiver = call.receiver()?;
            if let Some(inner_call) = receiver.as_call_node() {
                let mut alias = self.predicate_alias_from_call(&inner_call, environment)?;
                alias.negated = !alias.negated;
                return Some(alias);
            }
            let local = receiver.as_local_variable_read_node()?;
            let name = prism::constant_name(local.name());
            if let Some(alias) = environment.predicate_alias(&name) {
                Some(PredicateAlias {
                    source: alias.source.clone(),
                    negated: !alias.negated,
                    expected: alias.expected.clone(),
                })
            } else {
                Some(PredicateAlias {
                    source: name,
                    negated: true,
                    expected: None,
                })
            }
        } else {
            self.predicate_alias_from_call(&call, environment)
        }
    }

    pub(super) fn predicate_alias_from_call<'node>(
        &self,
        call: &CallNode<'node>,
        environment: &Environment,
    ) -> Option<PredicateAlias> {
        let name = prism::constant_name(call.name());
        if !matches!(
            name.as_str(),
            "nil?" | "is_a?" | "kind_of?" | "instance_of?"
        ) {
            return None;
        }
        let receiver = call.receiver()?;
        let local = receiver.as_local_variable_read_node()?;
        let source = prism::constant_name(local.name());
        let expected = if name == "nil?" {
            Type::Nil
        } else {
            let arguments = call
                .arguments()
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            if arguments.is_empty() {
                return None;
            }
            self.predicate_expected_type(&arguments[0], environment)
        };
        Some(PredicateAlias {
            source,
            negated: false,
            expected: Some(expected),
        })
    }

    pub(super) fn equality_predicate_narrowing<'node>(
        &mut self,
        name: &str,
        current: &Type,
        arguments: &[Node<'node>],
        truthy: bool,
        environment: &Environment,
    ) -> Option<Type> {
        if !matches!(name, "==" | "!=" | "equal?" | "eql?") || arguments.len() != 1 {
            return None;
        }
        let argument_type = self.node_type(&arguments[0], environment);
        let singleton = matches!(argument_type, Type::Nil | Type::True | Type::False);
        Some(match (name, truthy) {
            ("==" | "equal?" | "eql?", true) | ("!=", false) => current.meet(&argument_type),
            ("==" | "equal?" | "eql?", false) | ("!=", true) if singleton => {
                current.without(&argument_type)
            }
            ("==" | "equal?" | "eql?", false) | ("!=", true) => current.clone(),
            _ => current.clone(),
        })
    }

    pub(super) fn predicate_expected_type<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Type {
        if let Some(call) = node.as_call_node() {
            if prism::constant_name(call.name()) == "unsafe"
                && call.receiver().as_ref().is_some_and(|receiver| {
                    self.constant_reference_name(receiver)
                        .is_some_and(|name| name.trim_start_matches("::") == "T")
                })
            {
                // `T.unsafe(x)` deliberately erases the expression's type.
                // In particular, `klass <= T.unsafe(Integer)` must not
                // refine a class object to `Class[Integer]`.
                return Type::Any;
            }
            if prism::constant_name(call.name()) == "class"
                && call
                    .receiver()
                    .as_ref()
                    .is_some_and(|receiver| receiver.as_self_node().is_some())
            {
                return environment.self_type.clone();
            }
        }
        let type_ = signature::parse_type(&prism::text(self.source, node));
        let owner = self.lexical_owner(environment);
        match self.resolve_type_names(&type_, owner.as_deref()) {
            Type::Named(name, arguments)
                if arguments.is_empty()
                    && (name_matches(&name, "Class") || name_matches(&name, "Module")) =>
            {
                Type::Named(name, vec![Type::Anything])
            }
            type_ => type_,
        }
    }

    pub(super) fn safe_navigation_method_returns_non_nil<'node>(
        &mut self,
        receiver: &Node<'node>,
        receiver_type: &Type,
        name: &str,
        arguments: &[Node<'node>],
        environment: &mut Environment,
    ) -> bool {
        let receiver_type = receiver_type.without(&Type::Nil);
        if receiver_type.is_any() {
            return false;
        }
        if let Some(key) =
            self.receiver_method_key(Some(receiver), &receiver_type, name, environment)
        {
            if let Some(resolved) = self.resolve_method_key(&key) {
                if let Some(state) = self.declarations.methods.get(&resolved) {
                    let return_type = state.call_signature().return_type;
                    return !return_type.is_any() && return_type.without(&Type::Nil) == return_type;
                }
            }
        }
        let site = CallSite {
            argument_nodes: arguments,
            argument_types: &[],
            block: None,
        };
        let return_type = self.eval_method_call(&receiver_type, name, &site, environment);
        !return_type.is_any() && return_type.without(&Type::Nil) == return_type
    }

    pub(super) fn refine_local_array_write(
        &self,
        receiver_node: Option<&Node<'_>>,
        name: &str,
        argument_types: &[Type],
        receiver_type: &Type,
        environment: &mut Environment,
    ) {
        if !matches!(name, "push" | "<<" | "prepend") {
            return;
        }
        let Some(local) = receiver_node.and_then(Node::as_local_variable_read_node) else {
            return;
        };
        let Type::Array(element) = receiver_type else {
            return;
        };
        let open_array = environment
            .open_array_locals
            .contains(&prism::constant_name(local.name()));
        let mut refined_element = element.as_ref().clone();
        for actual in argument_types {
            if !open_array && !self.is_assignable(actual, element) {
                continue;
            }
            if refined_element.is_any() && !actual.is_any() {
                refined_element = actual.clone();
            } else {
                refined_element = refined_element.join(actual);
            }
        }
        if refined_element != element.as_ref().clone() {
            environment.bind(
                prism::constant_name(local.name()),
                Type::Array(Box::new(refined_element)),
            );
            if open_array {
                environment
                    .open_array_locals
                    .insert(prism::constant_name(local.name()));
            }
        }
    }

    pub(super) fn refine_local_hash_write(
        &self,
        receiver_node: Option<&Node<'_>>,
        name: &str,
        argument_types: &[Type],
        receiver_type: &Type,
        environment: &mut Environment,
    ) {
        if name != "[]=" {
            return;
        }
        let Some(local) = receiver_node.and_then(Node::as_local_variable_read_node) else {
            return;
        };
        let Type::Hash(key, value) = receiver_type else {
            return;
        };
        let Some(actual_key) = argument_types.first() else {
            return;
        };
        let Some(actual_value) = argument_types.last() else {
            return;
        };
        let refined_key = if key.is_any() && !actual_key.is_any() {
            actual_key.clone()
        } else {
            key.join(actual_key)
        };
        let refined_value = if value.is_any() && !actual_value.is_any() {
            actual_value.clone()
        } else {
            value.join(actual_value)
        };
        if refined_key != key.as_ref().clone() || refined_value != value.as_ref().clone() {
            environment.bind(
                prism::constant_name(local.name()),
                Type::Hash(Box::new(refined_key), Box::new(refined_value)),
            );
        }
    }
}
