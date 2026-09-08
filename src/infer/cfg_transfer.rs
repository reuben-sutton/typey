use super::{
    ivar_refinement_key, Analyzer, Environment, Eval, Flow, FlowKind, HirCallView, SharedKey,
};
use crate::cfg;
use crate::hir::{self, ArrayElement, ExprKind, HashElement, Literal, Read};
use crate::prism;
use crate::types::Type;
use ruby_prism::{IfNode, Node};

/// The inference-side state at a CFG block boundary.
///
/// CFG construction remains type-free. This state is the first boundary where
/// value IDs, environments, and abrupt flow outcomes become abstract facts
/// that can be joined by the generic CFG worklist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BlockState {
    values: Vec<Option<Type>>,
    environment: Environment,
    flow: Flow,
}

impl BlockState {
    fn with_values(environment: Environment, values: Vec<Option<Type>>, flow: Flow) -> Self {
        Self {
            values,
            environment,
            flow,
        }
    }

    fn join(&self, other: &Self) -> Self {
        let environment = match (
            self.flow.contains(FlowKind::Normal),
            other.flow.contains(FlowKind::Normal),
        ) {
            (true, false) => self.environment.clone(),
            (false, true) => other.environment.clone(),
            _ => self.environment.join(&other.environment),
        };
        let values = (0..self.values.len().max(other.values.len()))
            .map(
                |index| match (self.values.get(index), other.values.get(index)) {
                    (Some(Some(left)), Some(Some(right))) => Some(left.join(right)),
                    _ => None,
                },
            )
            .collect();
        Self {
            values,
            environment,
            flow: self.flow.union(other.flow),
        }
    }
}

impl<'src> Analyzer<'src> {
    /// Transfer value-producing HIR operations whose semantics do not depend
    /// on a method dispatch. The Prism node is retained only for source
    /// recording and inline assertions; the operation kind and read place
    /// come from owned HIR.
    pub(super) fn eval_cfg_value_dispatch<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let kind = self.hir_value_kind_for_node(node)?;
        match kind {
            ExprKind::Nil
            | ExprKind::Literal(_)
            | ExprKind::Read(_)
            | ExprKind::Array(_)
            | ExprKind::Hash(_) => {
                self.cfg_transfer_values = self.cfg_transfer_values.saturating_add(1);
                Some(self.transfer_cfg_value(node, kind, environment))
            }
            _ => None,
        }
    }

    fn hir_value_kind_for_node(&self, node: &Node<'_>) -> Option<ExprKind> {
        let span = prism::span(node);
        let expression_id = self.hir_value_ids.get(&span)?;
        let expression = self.hir_program.expression(*expression_id)?;
        match &expression.kind {
            ExprKind::Nil
            | ExprKind::Literal(_)
            | ExprKind::Read(_)
            | ExprKind::Array(_)
            | ExprKind::Hash(_) => Some(expression.kind.clone()),
            _ => None,
        }
    }

    fn transfer_cfg_value<'node>(
        &mut self,
        node: &Node<'node>,
        kind: ExprKind,
        environment: &mut Environment,
    ) -> Eval {
        let type_ = match kind {
            ExprKind::Nil => Type::Nil,
            ExprKind::Literal(literal) => Self::cfg_literal_type(&literal),
            ExprKind::Read(read) => self.transfer_cfg_read(node, read, environment),
            ExprKind::Array(elements) => {
                return self.transfer_cfg_array(node, elements, environment);
            }
            ExprKind::Hash(elements) => {
                return self.transfer_cfg_hash(node, elements, environment);
            }
            _ => unreachable!("non-value HIR operation reached CFG value transfer"),
        };
        Eval::value(self.record(node, type_))
    }

    fn transfer_cfg_array<'node>(
        &mut self,
        node: &Node<'node>,
        elements: Vec<ArrayElement>,
        environment: &mut Environment,
    ) -> Eval {
        let Some(array) = node.as_array_node() else {
            return Eval::value(self.record(node, Type::Any));
        };
        let prism_elements = array.elements().into_iter().collect::<Vec<_>>();
        if prism_elements.len() != elements.len() {
            return Eval::value(self.record(node, Type::Any));
        }

        let tuple_depth = self.literal_tuple_depth;
        self.literal_tuple_depth += 1;
        let mut element_types = Vec::new();
        let mut fixed_length = true;
        let mut element = Type::Never;
        for (hir_element, prism_element) in elements.into_iter().zip(prism_elements) {
            let (value_node, splat) = match hir_element {
                ArrayElement::Value(_) => (prism_element, false),
                ArrayElement::Splat(_) => {
                    let value_node = prism_element
                        .as_splat_node()
                        .and_then(|splat| splat.expression())
                        .unwrap_or(prism_element);
                    (value_node, true)
                }
            };
            let child_type = self.eval_node(&value_node, environment).type_;
            let child_type = if splat {
                fixed_length = false;
                self.array_element_type(&child_type)
            } else {
                child_type
            };
            element_types.push(child_type.clone());
            element = element.join(&child_type);
        }
        self.literal_tuple_depth = tuple_depth;
        let element = if element.is_never() {
            if (self.preserve_literal_tuples || self.preserve_nested_literal_tuples)
                && tuple_depth > 0
            {
                Type::Never
            } else {
                Type::Any
            }
        } else {
            element
        };
        let inferred = if fixed_length
            && ((self.preserve_literal_tuples && tuple_depth == 0)
                || (self.preserve_nested_literal_tuples && tuple_depth > 0)
                || self.expected_return_type.as_ref().is_some_and(|expected| {
                    tuple_depth == 0
                        && matches!(expected, Type::Tuple(elements) if elements.len() == element_types.len())
                }))
        {
            Type::Tuple(element_types)
        } else {
            Type::Array(Box::new(element))
        };
        let type_ = self.apply_inline_assertion_in_environment(node, inferred, environment);
        Eval::value(self.record(node, type_))
    }

    fn transfer_cfg_hash<'node>(
        &mut self,
        node: &Node<'node>,
        elements: Vec<HashElement>,
        environment: &mut Environment,
    ) -> Eval {
        let prism_elements = if let Some(hash) = node.as_hash_node() {
            hash.elements().into_iter().collect::<Vec<_>>()
        } else if let Some(hash) = node.as_keyword_hash_node() {
            hash.elements().into_iter().collect::<Vec<_>>()
        } else {
            return Eval::value(self.record(node, Type::Any));
        };
        if prism_elements.len() != elements.len() {
            return Eval::value(self.record(node, Type::Any));
        }

        let mut key = Type::Never;
        let mut value = Type::Never;
        for (hir_element, prism_element) in elements.into_iter().zip(prism_elements) {
            match hir_element {
                HashElement::Pair { .. } => {
                    let Some(assoc) = prism_element.as_assoc_node() else {
                        return Eval::value(self.record(node, Type::Any));
                    };
                    key = key.join(&self.eval_node(&assoc.key(), environment).type_);
                    value = value.join(&self.eval_node(&assoc.value(), environment).type_);
                }
                HashElement::Splat(_) => {
                    let Some(splat) = prism_element.as_assoc_splat_node() else {
                        return Eval::value(self.record(node, Type::Any));
                    };
                    if let Some(expression) = splat.value() {
                        match self.eval_node(&expression, environment).type_ {
                            Type::Hash(splat_key, splat_value) => {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                            }
                            Type::Any => {
                                key = Type::Any;
                                value = Type::Any;
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        let key = if key.is_never() { Type::Any } else { key };
        let value = if value.is_never() { Type::Any } else { value };
        let type_ = self.apply_inline_assertion_in_environment(
            node,
            Type::Hash(Box::new(key), Box::new(value)),
            environment,
        );
        Eval::value(self.record(node, type_))
    }

    fn cfg_literal_type(literal: &Literal) -> Type {
        match literal {
            Literal::Nil => Type::Nil,
            Literal::True => Type::True,
            Literal::False => Type::False,
            Literal::Integer(_) => Type::Integer,
            Literal::Float(_) => Type::Float,
            Literal::Rational(_) => Type::named("Rational"),
            Literal::Imaginary(_) => Type::named("Complex"),
            Literal::String(_) | Literal::XString(_) => Type::String,
            Literal::Symbol(_) => Type::Symbol,
            Literal::RegularExpression(_) => Type::named("Regexp"),
        }
    }

    fn transfer_cfg_read(
        &mut self,
        node: &Node<'_>,
        read: Read,
        environment: &mut Environment,
    ) -> Type {
        match read {
            Read::Local(local) => {
                let name = self
                    .hir_program
                    .local_name(local)
                    .map_or_else(String::new, |name| name.as_str().to_owned());
                self.apply_inline_assertion_in_environment(
                    node,
                    environment.get(&name),
                    environment,
                )
            }
            Read::InstanceVariable(name) => {
                let actual = self.ivar_type(environment, name.as_str());
                self.apply_inline_assertion_in_environment(node, actual, environment)
            }
            Read::ClassVariable(name) => {
                let actual = self.class_var_type(environment, name.as_str());
                self.apply_inline_assertion(node, actual)
            }
            Read::Global(name) => {
                let name = name.as_str().to_owned();
                self.record_shared_read(SharedKey::Global(name.clone()), environment);
                self.apply_inline_assertion(
                    node,
                    self.globals.get(&name).cloned().unwrap_or(Type::Any),
                )
            }
            Read::Constant(path) => {
                let name = path.as_str().to_owned();
                let actual = self.constant_type(environment, &name);
                self.report_missing_constant_if_needed(node, environment, &name);
                self.apply_inline_assertion(node, actual)
            }
            Read::SelfValue => self.apply_inline_assertion(node, environment.self_type.clone()),
            Read::Numbered(number) => {
                self.apply_inline_assertion(node, environment.get(&format!("_{number}")))
            }
            Read::It => self.apply_inline_assertion(node, environment.get("it")),
            Read::BackReference(_) => self.apply_inline_assertion(node, Type::Any),
        }
    }

    pub(super) fn has_cfg_call_operation(&self, node: &Node<'_>) -> bool {
        self.cfg_index
            .as_ref()
            .is_some_and(|index| index.has_call(prism::span(node)))
    }

    pub(super) fn has_cfg_assignment_operation(&self, node: &Node<'_>) -> bool {
        let span = prism::span(node);
        self.cfg_index
            .as_ref()
            .is_some_and(|index| index.has_call(span) || index.has_write(span))
    }

    fn cfg_conditional_for_node(&self, node: &Node<'_>) -> Option<cfg::Conditional> {
        self.cfg_index
            .as_ref()
            .and_then(|index| index.conditional(prism::span(node)))
            .cloned()
    }

    pub(super) fn report_cfg_fallback(&self, node: &Node<'_>, kind: &str) {
        if self.config.debug {
            eprintln!(
                "[typey] CFG fallback for {kind} at {:?}: no owned transfer is available",
                prism::span(node)
            );
        }
    }

    pub(super) fn transfer_cfg_call<'node>(
        &mut self,
        node: &Node<'node>,
        call: HirCallView<'node>,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_calls = self.cfg_transfer_calls.saturating_add(1);
        // The CFG supplies the dispatch name and argument-shape operation.
        // HirCallView retains only Prism child nodes so the existing transfer
        // machinery can evaluate child expressions until the owned value
        // evaluator lands.
        self.eval_call_result(node, &call, environment)
    }

    pub(super) fn transfer_cfg_assignment<'node>(
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
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
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
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
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
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Global(name) => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_global(name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Constant(name) => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
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

    pub(super) fn eval_if_dispatch<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if self.config.enable_cfg {
            if let Some(conditional) = self.cfg_conditional_for_node(node) {
                return self.transfer_cfg_if(node, if_node, conditional, environment);
            }
            self.cfg_transfer_fallbacks = self.cfg_transfer_fallbacks.saturating_add(1);
            self.report_cfg_fallback(node, "conditional");
        }
        self.eval_if(node, if_node, environment)
    }

    fn transfer_cfg_if<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        conditional: cfg::Conditional,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_conditionals = self.cfg_transfer_conditionals.saturating_add(1);
        let predicate = if_node.predicate();
        let then_node = if_node.statements().map(|statements| statements.as_node());
        let subsequent = if_node.subsequent();
        self.eval_cfg_conditional_paths(
            node,
            &predicate,
            then_node,
            subsequent,
            if_node,
            conditional,
            environment,
        )
    }

    fn eval_cfg_conditional_paths<'node>(
        &mut self,
        node: &Node<'node>,
        predicate: &Node<'node>,
        then_node: Option<Node<'node>>,
        subsequent: Option<Node<'node>>,
        if_node: &IfNode<'node>,
        conditional: cfg::Conditional,
        environment: &mut Environment,
    ) -> Eval {
        debug_assert_ne!(conditional.truthy, conditional.falsy);
        debug_assert_ne!(conditional.join, conditional.truthy);
        debug_assert_ne!(conditional.join, conditional.falsy);

        let previous_defer_inline_assertions = self.defer_inline_assertions;
        self.defer_inline_assertions = true;
        let predicate_type = self
            .eval_node(predicate, environment)
            .normal_type
            .unwrap_or(Type::Never);
        self.defer_inline_assertions = previous_defer_inline_assertions;
        let (then_reachable, else_reachable) =
            self.predicate_reachability(predicate, environment, &predicate_type);
        let report_unreachable = self.should_report_unreachable_branch(node)
            && self.predicate_is_precise(predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(predicate, &mut then_environment, true);
        if !then_reachable && report_unreachable {
            if let Some(statements) = if_node.statements() {
                if let Some(first) = statements.body().into_iter().next() {
                    self.error(&first, "This code is unreachable");
                }
            }
        }
        let then_result = then_node.map_or_else(
            || Eval::value(Type::Nil),
            |then_node| self.eval_node(&then_node, &mut then_environment),
        );
        let then_result = if then_reachable {
            then_result
        } else {
            Eval::unreachable()
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(predicate, &mut else_environment, false);
        let else_result = if let Some(subsequent) = subsequent {
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

        let joined_state =
            BlockState::with_values(then_environment, Vec::new(), then_result.flow).join(
                &BlockState::with_values(else_environment, Vec::new(), else_result.flow),
            );
        *environment = joined_state.environment;
        let mut result = Eval::combine(&then_result, &else_result);
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment(name: &str, type_: Type) -> Environment {
        let mut environment = Environment::default();
        environment.bind(name, type_);
        environment
    }

    #[test]
    fn normal_path_wins_over_an_abrupt_path() {
        let normal = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let returned = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::abrupt(FlowKind::Return),
        );

        let joined = normal.join(&returned);

        assert_eq!(joined.environment.get("value"), Type::String);
        assert_eq!(joined.values, vec![Some(Type::String.join(&Type::Integer))]);
        assert!(joined.flow.contains(FlowKind::Normal));
        assert!(joined.flow.contains(FlowKind::Return));
    }

    #[test]
    fn two_normal_paths_join_values_and_environment_facts() {
        let left = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::normal(),
        );

        let joined = left.join(&right);

        let expected = Type::String.join(&Type::Integer);
        assert_eq!(joined.environment.get("value"), expected);
        assert_eq!(joined.values, vec![Some(expected)]);
    }

    #[test]
    fn missing_value_on_one_edge_is_not_invented_at_the_join() {
        let left = BlockState::with_values(
            Environment::default(),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(Environment::default(), vec![None], Flow::normal());

        assert_eq!(left.join(&right).values, vec![None]);
    }
}
