//! Parser-backed control-flow transfer retained for the legacy evaluator.
//!
//! CFG transfer owns the new HIR control-flow path. These routines are the
//! compatibility adapter for bodies that still run through Prism nodes, and
//! are kept separate from the analyzer coordinator so the two paths do not
//! become interleaved again.

use super::*;
use ruby_prism::{IfNode, UnlessNode};

impl<'src> Analyzer<'src> {
    pub(super) fn eval_if<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = if_node.predicate();
        let previous_defer_inline_assertions = self.defer_inline_assertions;
        self.defer_inline_assertions = true;
        let predicate_type = self
            .eval_node(&predicate, environment)
            .normal_type
            .unwrap_or(Type::Never);
        self.defer_inline_assertions = previous_defer_inline_assertions;
        let (then_reachable, else_reachable) =
            self.predicate_reachability(&predicate, environment, &predicate_type);
        let report_unreachable = self.should_report_unreachable_branch(node)
            && self.predicate_is_precise(&predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut then_environment, true);
        let then_result = if let Some(statements) = if_node.statements() {
            if !then_reachable && report_unreachable {
                if let Some(first) = statements.body().into_iter().next() {
                    self.error(&first, "This code is unreachable");
                }
            }
            self.eval_statements(&statements, &mut then_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let then_result = if then_reachable {
            then_result
        } else {
            // Keep checking an unreachable branch for diagnostics and reveals,
            // but do not let its flow affect the enclosing expression.
            Eval::unreachable()
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut else_environment, false);
        let else_result = if let Some(subsequent) = if_node.subsequent() {
            if !else_reachable && report_unreachable {
                if let Some(else_clause) = subsequent.as_else_node() {
                    if let Some(statements) = else_clause.statements() {
                        if let Some(first) = statements.body().into_iter().next() {
                            self.error(&first, "This code is unreachable");
                        }
                    }
                }
            }
            self.eval_alternative(&subsequent, &mut else_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let else_result = if else_reachable {
            else_result
        } else {
            Eval::unreachable()
        };

        *environment = self.join_flow_environments(
            &then_environment,
            then_result.flow,
            &else_environment,
            else_result.flow,
        );
        let mut result = Eval::combine(&then_result, &else_result);
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    pub(super) fn eval_unless<'node>(
        &mut self,
        node: &Node<'node>,
        unless: &UnlessNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = unless.predicate();
        let previous_defer_inline_assertions = self.defer_inline_assertions;
        self.defer_inline_assertions = true;
        let predicate_type = self
            .eval_node(&predicate, environment)
            .normal_type
            .unwrap_or(Type::Never);
        self.defer_inline_assertions = previous_defer_inline_assertions;
        let (predicate_truthy, predicate_falsy) =
            self.predicate_reachability(&predicate, environment, &predicate_type);
        let then_reachable = predicate_falsy;
        let else_reachable = predicate_truthy;
        let report_unreachable = self.should_report_unreachable_branch(node)
            && self.predicate_is_precise(&predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut then_environment, false);
        let then_result = if let Some(statements) = unless.statements() {
            if !then_reachable && report_unreachable {
                if let Some(first) = statements.body().into_iter().next() {
                    self.error(&first, "This code is unreachable");
                }
            }
            self.eval_statements(&statements, &mut then_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let then_result = if then_reachable {
            then_result
        } else {
            Eval::value(Type::Never)
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut else_environment, true);
        let else_result = if let Some(else_clause) = unless.else_clause() {
            if let Some(statements) = else_clause.statements() {
                if !else_reachable && report_unreachable {
                    if let Some(first) = statements.body().into_iter().next() {
                        self.error(&first, "This code is unreachable");
                    }
                }
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            Eval::value(Type::Nil)
        };
        let else_result = if else_reachable {
            else_result
        } else {
            Eval::value(Type::Never)
        };

        *environment = self.join_flow_environments(
            &then_environment,
            then_result.flow,
            &else_environment,
            else_result.flow,
        );
        let mut result = Eval::combine(&then_result, &else_result);
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    pub(super) fn eval_control_arguments<'node>(
        &mut self,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        environment: &mut Environment,
    ) -> Type {
        let Some(arguments) = arguments else {
            return Type::Nil;
        };
        let mut result = Type::Nil;
        for argument in &arguments.arguments() {
            result = self.eval_node(&argument, environment).type_;
        }
        result
    }

    pub(super) fn eval_loop<'node>(
        &mut self,
        predicate: &Node<'node>,
        statements: Option<&ruby_prism::StatementsNode<'node>>,
        environment: &mut Environment,
        predicate_truthy: bool,
    ) -> Eval {
        let entry = environment.clone();
        let mut head = entry.clone();
        let mut exit_environment: Option<Environment> = None;
        let mut break_type = Type::Never;
        let mut abrupt = OutcomeTypes::default();
        let mut terminal_flow = Flow::empty();
        loop {
            let mut condition_environment = head.clone();
            let condition_result = self.eval_node(predicate, &mut condition_environment);
            abrupt = abrupt.join(
                &condition_result
                    .abrupt
                    .without(FlowKind::Break)
                    .without(FlowKind::Next),
            );
            terminal_flow = terminal_flow.union(
                condition_result
                    .flow
                    .without(FlowKind::Normal)
                    .without(FlowKind::Break)
                    .without(FlowKind::Next),
            );
            if !condition_result.flow.contains(FlowKind::Normal) {
                break;
            }
            exit_environment = Some(match exit_environment {
                Some(current) => current.join(&condition_environment),
                None => condition_environment.clone(),
            });
            let mut body_environment = condition_environment;
            self.narrow_from_predicate(predicate, &mut body_environment, predicate_truthy);
            let body_result = statements.map_or_else(
                || Eval::value(Type::Nil),
                |statements| self.eval_statements(statements, &mut body_environment),
            );
            let body_terminal_flow = body_result
                .flow
                .without(FlowKind::Normal)
                .without(FlowKind::Break)
                .without(FlowKind::Next);
            terminal_flow = terminal_flow.union(body_terminal_flow);
            if !body_terminal_flow.is_empty() {
                abrupt = abrupt.join(
                    &body_result
                        .abrupt
                        .without(FlowKind::Break)
                        .without(FlowKind::Next),
                );
            }
            if body_result.flow.contains(FlowKind::Break) {
                break_type = break_type.join(&body_result.abrupt.break_type);
                exit_environment = Some(match exit_environment {
                    Some(current) => current.join(&body_environment),
                    None => body_environment.clone(),
                });
            }
            if !body_result.flow.contains(FlowKind::Normal)
                && !body_result.flow.contains(FlowKind::Next)
            {
                break;
            }
            let next = head.join(&body_environment);
            if next == head {
                break;
            }
            head = next;
        }
        let mut result_environment = entry.join(&head);
        if let Some(exit_environment) = exit_environment {
            result_environment = result_environment.join(&exit_environment);
        }
        *environment = result_environment;
        let normal_type = Type::union([Type::Nil, break_type]);
        Eval::from_parts(
            Some(normal_type),
            abrupt,
            Flow::normal().union(terminal_flow),
        )
    }

    pub(super) fn eval_for<'node>(
        &mut self,
        node: &Node<'node>,
        for_node: &ruby_prism::ForNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let collection = for_node.collection();
        let collection_result = self.eval_node(&collection, environment);
        if !collection_result.flow.contains(FlowKind::Normal) {
            let mut collection_result = collection_result;
            collection_result.type_ = self.record(node, collection_result.type_.clone());
            return collection_result;
        }
        let collection_type = collection_result.type_;
        let element_type = self.array_element_type(&collection_type);
        let entry = environment.clone();
        let mut head = entry.clone();
        let mut exit_environment: Option<Environment> = None;
        let mut break_type = Type::Never;
        let mut abrupt = collection_result
            .abrupt
            .without(FlowKind::Break)
            .without(FlowKind::Next);
        let mut terminal_flow = collection_result
            .flow
            .without(FlowKind::Normal)
            .without(FlowKind::Break)
            .without(FlowKind::Next);
        loop {
            let mut body_environment = head.clone();
            self.bind_for_target(
                &for_node.index(),
                element_type.clone(),
                &mut body_environment,
            );
            let body_result = for_node.statements().map_or_else(
                || Eval::value(Type::Nil),
                |statements| self.eval_statements(&statements, &mut body_environment),
            );
            let body_terminal_flow = body_result
                .flow
                .without(FlowKind::Normal)
                .without(FlowKind::Break)
                .without(FlowKind::Next);
            terminal_flow = terminal_flow.union(body_terminal_flow);
            if !body_terminal_flow.is_empty() {
                abrupt = abrupt.join(
                    &body_result
                        .abrupt
                        .without(FlowKind::Break)
                        .without(FlowKind::Next),
                );
            }
            if body_result.flow.contains(FlowKind::Break) {
                break_type = break_type.join(&body_result.abrupt.break_type);
                exit_environment = Some(match exit_environment {
                    Some(current) => current.join(&body_environment),
                    None => body_environment.clone(),
                });
            }
            if !body_result.flow.contains(FlowKind::Normal)
                && !body_result.flow.contains(FlowKind::Next)
            {
                break;
            }
            let next = head.join(&body_environment);
            if next == head {
                break;
            }
            head = next;
        }
        let mut result_environment = entry.join(&head);
        if let Some(exit_environment) = exit_environment {
            result_environment = result_environment.join(&exit_environment);
        }
        *environment = result_environment;
        let normal_type = Type::union([Type::Nil, break_type]);
        let mut result = Eval::from_parts(
            Some(normal_type),
            abrupt,
            Flow::normal().union(terminal_flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    pub(super) fn bind_for_target<'node>(
        &mut self,
        target: &Node<'node>,
        type_: Type,
        environment: &mut Environment,
    ) {
        if let Some(target) = target.as_instance_variable_target_node() {
            let name = prism::constant_name(target.name());
            let target_node = target.as_node();
            let type_ =
                self.apply_inline_assertion_in_environment(&target_node, type_, environment);
            // Empty arrays in a tuple-style multi-assignment are open
            // containers. Their element type is bottom only until the first
            // write; retaining `Never` here would make a later append reject
            // every concrete value.
            let type_ = if matches!(&type_, Type::Array(element) if element.is_never()) {
                Type::Array(Box::new(Type::Any))
            } else {
                type_
            };
            self.observe_ivar(environment, name.clone(), &type_, false);
            environment.bind(ivar_refinement_key(&name), type_);
            return;
        }
        if let Some(write) = target.as_local_variable_write_node() {
            let name = prism::constant_name(write.name());
            let open_array = matches!(&type_, Type::Array(element) if element.is_never());
            environment.bind(name.clone(), type_);
            if open_array {
                environment.open_array_locals.insert(name);
            }
            return;
        }
        if let Some(target) = target.as_local_variable_target_node() {
            let name = prism::constant_name(target.name());
            let open_array = matches!(&type_, Type::Array(element) if element.is_never());
            environment.bind(name.clone(), type_);
            if open_array {
                environment.open_array_locals.insert(name);
            }
            return;
        }
        if let Some(required) = target.as_required_parameter_node() {
            environment.bind(prism::constant_name(required.name()), type_);
            return;
        }
        if let Some(multi) = target.as_multi_target_node() {
            let lefts = multi.lefts().into_iter().collect::<Vec<_>>();
            let rights = multi.rights().into_iter().collect::<Vec<_>>();
            let known_length = match &type_ {
                Type::Tuple(elements) => Some(elements.len()),
                _ => None,
            };
            for (index, child) in lefts.iter().enumerate() {
                self.bind_for_target(
                    child,
                    self.multi_assignment_element_type(&type_, index, known_length),
                    environment,
                );
            }
            if let Some(rest) = multi.rest() {
                self.bind_for_target(
                    &rest,
                    Type::Array(Box::new(self.array_element_type(&type_))),
                    environment,
                );
            }
            let right_start = known_length
                .map(|length| lefts.len().max(length.saturating_sub(rights.len())))
                .unwrap_or(lefts.len());
            for (index, child) in rights.iter().enumerate() {
                self.bind_for_target(
                    child,
                    self.multi_assignment_element_type(&type_, right_start + index, known_length),
                    environment,
                );
            }
        }
    }

    pub(super) fn multi_assignment_element_type(
        &self,
        type_: &Type,
        index: usize,
        known_length: Option<usize>,
    ) -> Type {
        match type_ {
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.multi_assignment_element_type(member, index, known_length)),
            ),
            Type::Tuple(elements) => elements.get(index).cloned().unwrap_or(Type::Nil),
            Type::Array(element) => {
                if known_length.is_some_and(|length| index >= length) {
                    Type::Nil
                } else if known_length.is_some() {
                    element.as_ref().clone()
                } else {
                    Type::union([element.as_ref().clone(), Type::Nil])
                }
            }
            Type::Nil => Type::Nil,
            Type::Any => Type::Any,
            _ => Type::Any,
        }
    }
}
