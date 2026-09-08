//! Narrow Prism adapters retained by the recursive evaluator.
//!
//! Owned CFG transfer must not depend on these helpers. They exist only where
//! the legacy evaluator still needs a parser child node while the equivalent
//! HIR operation is already available for identity and dispatch decisions.

use super::*;

impl<'src> Analyzer<'src> {
    /// Parser-facing entry point for the owned CFG transfer. The transfer
    /// itself consumes only `SourceSite`, HIR, and CFG values; this adapter is
    /// kept with the recursive evaluator's Prism compatibility boundary.
    pub(in crate::infer) fn eval_cfg_body_from_prism<'node>(
        &mut self,
        body_node: &Node<'node>,
        body_id: hir::BodyId,
        environment: &mut Environment,
        record_result: bool,
    ) -> Option<Eval> {
        let (start, end) = prism::span(body_node);
        self.eval_cfg_body_owned(
            SourceSite::new(start, end),
            body_id,
            environment,
            record_result,
        )
    }

    /// Prism-facing adapter for value trees whose owned HIR transfer is
    /// already available. Recursive evaluation owns the parser lookup; the
    /// actual value semantics remain in `cfg_transfer/value.rs`.
    pub(in crate::infer) fn eval_cfg_value_dispatch<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let span = prism::span(node);
        let expression = *self.hir_value_ids.get(&span)?;
        if !Self::owned_value_tree_supported(&self.hir_program, expression) {
            return None;
        }
        self.cfg_transfer_values = self.cfg_transfer_values.saturating_add(1);
        Some(self.eval_owned_value(expression, environment))
    }

    pub(in crate::infer) fn transfer_cfg_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: hir::AssignTarget,
        value: hir::ExprId,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_assignments = self.cfg_transfer_assignments.saturating_add(1);
        if let Some(result) =
            self.transfer_cfg_set_assignment(node, target.clone(), value, &operator, environment)
        {
            return result;
        }
        self.eval_hir_assignment(node, target, value, operator, environment)
    }

    fn eval_cfg_assignment_value(
        &mut self,
        value_id: hir::ExprId,
        environment: &mut Environment,
    ) -> Option<Type> {
        Self::owned_value_tree_supported(&self.hir_program, value_id)
            .then(|| self.eval_owned_value(value_id, environment).type_)
    }

    fn transfer_cfg_set_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: hir::AssignTarget,
        value_id: hir::ExprId,
        operator: &hir::AssignOperator,
        environment: &mut Environment,
    ) -> Option<Eval> {
        if !matches!(operator, hir::AssignOperator::Set) {
            return None;
        }
        let value_node = self.assignment_value_node(node)?;
        debug_assert!(self.hir_program.expression(value_id).is_some());
        match target {
            hir::AssignTarget::Local(local) => {
                let name = self.hir_program.local_name(local)?.as_str().to_owned();
                let actual = self.eval_cfg_assignment_value(value_id, environment)?;
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                if let Some(alias) = self.predicate_alias_for_value(&value_node, environment) {
                    environment.bind_predicate_alias(name.clone(), type_.clone(), alias);
                } else {
                    environment.bind(name.clone(), type_.clone());
                }
                if value_node
                    .as_array_node()
                    .is_some_and(|array| array.elements().is_empty())
                    && matches!(&type_, Type::Array(element) if element.is_any())
                {
                    environment.open_array_locals.insert(name);
                }
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::InstanceVariable(name) => {
                let name = name.as_str().to_owned();
                let actual = self.eval_cfg_assignment_value(value_id, environment)?;
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                let type_ =
                    self.preserve_typed_empty_array_ivar(environment, &name, &value_node, type_);
                let provisional = value_node
                    .as_local_variable_read_node()
                    .is_some_and(|local| {
                        environment.is_provisional(&prism::constant_name(local.name()))
                    });
                self.observe_ivar(environment, name.clone(), &type_, provisional);
                environment.bind(ivar_refinement_key(&name), type_.clone());
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::ClassVariable(name) => {
                let actual = self.eval_cfg_assignment_value(value_id, environment)?;
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Global(name) => {
                let actual = self.eval_cfg_assignment_value(value_id, environment)?;
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_global(name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Constant(name) => {
                let actual = self.eval_cfg_assignment_value(value_id, environment)?;
                let name = name.as_str().to_owned();
                let struct_type = self.struct_subclass_type(environment, &value_node, &name);
                if let Some(struct_type) = struct_type.as_ref() {
                    self.eval_dynamic_struct_block(&value_node, struct_type, environment);
                }
                let type_ = self.apply_inline_assertion(node, struct_type.unwrap_or(actual));
                self.observe_constant(environment, name, &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. } => None,
        }
    }

    pub(super) fn hir_call_for_node(&self, node: &Node<'_>) -> Option<&hir::Call> {
        let span = prism::span(node);
        if let Some(expression_id) = self.hir_call_ids.get(&span) {
            if let Some(expression) = self.hir_program.expression(*expression_id) {
                if let hir::ExprKind::Call(call) = &expression.kind {
                    return Some(call);
                }
            }
        }
        self.hir_program
            .expressions
            .iter()
            .find_map(|expression| {
                let expression_span =
                    (expression.span.start as usize, expression.span.end as usize);
                (expression_span == span).then_some(&expression.kind)
            })
            .and_then(|kind| match kind {
                hir::ExprKind::Call(call) => Some(call),
                _ => None,
            })
    }

    pub(super) fn hir_call_view<'node>(
        &self,
        node: &Node<'_>,
        prism_call: CallNode<'node>,
    ) -> Option<HirCallView<'node>> {
        let span = prism::span(node);
        let expression_id = self.hir_call_ids.get(&span)?;
        let hir::ExprKind::Call(call) = &self
            .hir_program
            .expressions
            .get(expression_id.0 as usize)?
            .kind
        else {
            return None;
        };
        Some(HirCallView {
            call: call.clone(),
            prism_call,
        })
    }

    pub(super) fn hir_assignment_for_node(
        &self,
        node: &Node<'_>,
    ) -> Option<(hir::AssignTarget, hir::ExprId, hir::AssignOperator)> {
        let expression_id = self.hir_assignment_ids.get(&prism::span(node))?;
        let hir::ExprKind::Assign {
            target,
            value,
            operator,
            ..
        } = &self
            .hir_program
            .expressions
            .get(expression_id.0 as usize)?
            .kind
        else {
            return None;
        };
        Some((target.clone(), *value, operator.clone()))
    }

    /// Return the executable child of an assignment. The HIR target and
    /// operator determine the assignment semantics; this narrow Prism bridge
    /// only supplies the child node to the existing expression evaluator.
    pub(super) fn assignment_value_node<'node>(&self, node: &Node<'node>) -> Option<Node<'node>> {
        if let Some(write) = node.as_local_variable_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_local_variable_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_local_variable_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_local_variable_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_instance_variable_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_instance_variable_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_instance_variable_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_instance_variable_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_class_variable_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_class_variable_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_class_variable_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_class_variable_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_global_variable_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_global_variable_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_global_variable_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_global_variable_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_path_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_path_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_path_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_constant_path_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_index_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_index_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_index_or_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_call_operator_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_call_and_write_node() {
            return Some(write.value());
        }
        if let Some(write) = node.as_call_or_write_node() {
            return Some(write.value());
        }
        node.as_call_node().and_then(|call| {
            call.is_attribute_write()
                .then(|| call.arguments())
                .flatten()
                .and_then(|arguments| arguments.arguments().into_iter().last())
        })
    }

    pub(super) fn assignment_receiver_node<'node>(
        &self,
        node: &Node<'node>,
    ) -> Option<Option<Node<'node>>> {
        if let Some(call) = node.as_call_node() {
            return call.is_attribute_write().then(|| call.receiver());
        }
        if let Some(write) = node.as_call_operator_write_node() {
            return Some(write.receiver());
        }
        if let Some(write) = node.as_call_and_write_node() {
            return Some(write.receiver());
        }
        if let Some(write) = node.as_call_or_write_node() {
            return Some(write.receiver());
        }
        if let Some(write) = node.as_index_operator_write_node() {
            return Some(write.receiver());
        }
        if let Some(write) = node.as_index_and_write_node() {
            return Some(write.receiver());
        }
        if let Some(write) = node.as_index_or_write_node() {
            return Some(write.receiver());
        }
        None
    }

    pub(super) fn assignment_index_arguments<'node>(
        &self,
        node: &Node<'node>,
    ) -> Option<Option<ArgumentsNode<'node>>> {
        if let Some(write) = node.as_index_operator_write_node() {
            return Some(write.arguments());
        }
        if let Some(write) = node.as_index_and_write_node() {
            return Some(write.arguments());
        }
        if let Some(write) = node.as_index_or_write_node() {
            return Some(write.arguments());
        }
        None
    }
}
