//! Owned CFG transfer for direct storage assignments.

use super::super::{ivar_refinement_key, Analyzer, Environment, Eval};
use crate::hir;
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;

impl<'src> Analyzer<'src> {
    pub(in crate::infer) fn transfer_cfg_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: crate::hir::AssignTarget,
        value: crate::hir::ExprId,
        operator: crate::hir::AssignOperator,
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

    /// Transfer direct storage writes from owned HIR. Compound writes and
    /// attribute/index targets still use the established dispatch helpers
    /// until their read/branch/write sequence is driven by block state.
    fn eval_cfg_assignment_value<'node>(
        &mut self,
        value_id: hir::ExprId,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Type {
        if Self::owned_value_tree_supported(&self.hir_program, value_id) {
            self.eval_owned_value(value_id, environment).type_
        } else {
            Self::normal_type(self.eval_node(value_node, environment))
        }
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
                let actual = self.eval_cfg_assignment_value(value_id, &value_node, environment);
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
                let actual = self.eval_cfg_assignment_value(value_id, &value_node, environment);
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
                let actual = self.eval_cfg_assignment_value(value_id, &value_node, environment);
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Global(name) => {
                let actual = self.eval_cfg_assignment_value(value_id, &value_node, environment);
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_global(name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Constant(name) => {
                let actual = self.eval_cfg_assignment_value(value_id, &value_node, environment);
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
}
