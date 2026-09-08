//! Narrow Prism adapters retained by the recursive evaluator.
//!
//! Owned CFG transfer must not depend on these helpers. They exist only where
//! the legacy evaluator still needs a parser child node while the equivalent
//! HIR operation is already available for identity and dispatch decisions.

use super::*;

impl<'src> Analyzer<'src> {
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
