use super::cfg_state::BlockState;
use super::{
    ivar_refinement_key, Analyzer, Environment, Eval, Flow, FlowKind, HirCallView, OutcomeTypes,
    SharedKey, SourceSite,
};
use crate::cfg;
use crate::hir::{self, ArrayElement, ExprKind, HashElement, Literal, Read};
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;

mod body;
mod legacy;
mod patterns;
mod preflight;

fn cfg_global_refinement_key(name: &str) -> String {
    format!("\u{1}cfg-global:{name}")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CfgFallbackKind {
    UnsupportedOperation,
    UnsupportedEdge,
    LegacyBridge,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct CfgFallbackCounters {
    pub(super) unsupported_operation: usize,
    pub(super) unsupported_edge: usize,
    pub(super) legacy_bridge: usize,
}

impl CfgFallbackCounters {
    pub(super) fn record(&mut self, kind: CfgFallbackKind) {
        let counter = match kind {
            CfgFallbackKind::UnsupportedOperation => &mut self.unsupported_operation,
            CfgFallbackKind::UnsupportedEdge => &mut self.unsupported_edge,
            CfgFallbackKind::LegacyBridge => &mut self.legacy_bridge,
        };
        *counter = counter.saturating_add(1);
    }

    pub(super) fn total(&self) -> usize {
        self.unsupported_operation
            .saturating_add(self.unsupported_edge)
            .saturating_add(self.legacy_bridge)
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
        let expression = self.hir_value_expression_for_node(node)?;
        if !Self::owned_value_tree_supported(&self.hir_program, expression) {
            return None;
        }
        self.cfg_transfer_values = self.cfg_transfer_values.saturating_add(1);
        Some(self.eval_owned_value(expression, environment))
    }

    fn hir_value_expression_for_node(&self, node: &Node<'_>) -> Option<hir::ExprId> {
        let span = prism::span(node);
        let expression_id = self.hir_value_ids.get(&span)?;
        Some(*expression_id)
    }

    fn owned_value_tree_supported(program: &hir::Program, expression: hir::ExprId) -> bool {
        let Some(expression) = program.expression(expression) else {
            return false;
        };
        match &expression.kind {
            ExprKind::Nil | ExprKind::Literal(_) | ExprKind::Read(_) => true,
            ExprKind::Array(elements) => elements.iter().all(|element| match element {
                ArrayElement::Value(value) | ArrayElement::Splat { value, .. } => {
                    Self::owned_value_tree_supported(program, *value)
                }
            }),
            ExprKind::Hash(elements) => elements.iter().all(|element| match element {
                HashElement::Pair { key, value } => {
                    Self::owned_value_tree_supported(program, *key)
                        && Self::owned_value_tree_supported(program, *value)
                }
                HashElement::Splat { value, .. } => {
                    Self::owned_value_tree_supported(program, *value)
                }
            }),
            _ => false,
        }
    }

    fn eval_owned_value(&mut self, expression: hir::ExprId, environment: &mut Environment) -> Eval {
        let (span, kind) = {
            let expression = self
                .hir_program
                .expression(expression)
                .expect("owned value expression exists after preflight");
            (expression.span, expression.kind.clone())
        };
        let site = SourceSite::from_span(span, Some(expression));
        let type_ = match kind {
            ExprKind::Nil => Type::Nil,
            ExprKind::Literal(literal) => Self::cfg_literal_type(&literal),
            ExprKind::Read(read) => {
                let type_ = self.transfer_cfg_read_at(site, read, environment);
                return Eval::value(self.record_at(site, type_, false, None));
            }
            ExprKind::Array(elements) => return self.eval_owned_array(site, elements, environment),
            ExprKind::Hash(elements) => return self.eval_owned_hash(site, elements, environment),
            _ => unreachable!("non-value HIR operation reached owned value transfer"),
        };
        let type_ = self.apply_inline_assertion_in_environment_at(site, type_, environment);
        Eval::value(self.record_at(site, type_, false, None))
    }

    fn eval_owned_array(
        &mut self,
        site: SourceSite,
        elements: Vec<ArrayElement>,
        environment: &mut Environment,
    ) -> Eval {
        let tuple_depth = self.literal_tuple_depth;
        self.literal_tuple_depth += 1;
        let mut element_types = Vec::new();
        let mut fixed_length = true;
        let mut element = Type::Never;
        for element_value in elements {
            let (value, splat, splat_span) = match element_value {
                ArrayElement::Value(value) => (value, false, None),
                ArrayElement::Splat { value, span } => (value, true, Some(span)),
            };
            let child_type = self.eval_owned_value(value, environment).type_;
            if let Some(span) = splat_span {
                self.record_at(
                    SourceSite::from_span(span, None),
                    child_type.clone(),
                    false,
                    None,
                );
            }
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
        let type_ = self.apply_inline_assertion_in_environment_at(site, inferred, environment);
        Eval::value(self.record_at(site, type_, false, None))
    }

    fn eval_owned_hash(
        &mut self,
        site: SourceSite,
        elements: Vec<HashElement>,
        environment: &mut Environment,
    ) -> Eval {
        let mut key = Type::Never;
        let mut value = Type::Never;
        for element in elements {
            match element {
                HashElement::Pair {
                    key: key_id,
                    value: value_id,
                } => {
                    key = key.join(&self.eval_owned_value(key_id, environment).type_);
                    value = value.join(&self.eval_owned_value(value_id, environment).type_);
                }
                HashElement::Splat {
                    value: value_id, ..
                } => match self.eval_owned_value(value_id, environment).type_ {
                    Type::Hash(splat_key, splat_value) => {
                        key = key.join(&splat_key);
                        value = value.join(&splat_value);
                    }
                    Type::Any => {
                        key = Type::Any;
                        value = Type::Any;
                    }
                    _ => {}
                },
            }
        }
        let key = if key.is_never() { Type::Any } else { key };
        let value = if value.is_never() { Type::Any } else { value };
        let type_ = self.apply_inline_assertion_in_environment_at(
            site,
            Type::Hash(Box::new(key), Box::new(value)),
            environment,
        );
        Eval::value(self.record_at(site, type_, false, None))
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

    pub(super) fn transfer_cfg_read_at(
        &mut self,
        site: SourceSite,
        read: Read,
        environment: &mut Environment,
    ) -> Type {
        match read {
            Read::Local(local) => {
                let name = self
                    .hir_program
                    .local_name(local)
                    .map_or_else(String::new, |name| name.as_str().to_owned());
                self.apply_inline_assertion_in_environment_at(
                    site,
                    environment.get(&name),
                    environment,
                )
            }
            Read::InstanceVariable(name) => {
                let actual = self.ivar_type(environment, name.as_str());
                self.apply_inline_assertion_in_environment_at(site, actual, environment)
            }
            Read::ClassVariable(name) => {
                let actual = self.class_var_type(environment, name.as_str());
                self.apply_inline_assertion_at(site, actual)
            }
            Read::Global(name) => {
                let name = name.as_str().to_owned();
                self.record_shared_read(SharedKey::Global(name.clone()), environment);
                let actual = environment
                    .contains(&cfg_global_refinement_key(&name))
                    .then(|| environment.get(&cfg_global_refinement_key(&name)))
                    .unwrap_or_else(|| self.globals.get(&name).cloned().unwrap_or(Type::Any));
                self.apply_inline_assertion_at(site, actual)
            }
            Read::Constant(path) => {
                let name = path.as_str().to_owned();
                let actual = self.constant_type(environment, &name);
                if self.reports_missing_api_at(site) && !self.constant_is_known(environment, &name)
                {
                    self.error_at(
                        site,
                        format!(
                            "Unable to resolve constant `{}`",
                            name.trim_start_matches("::")
                        ),
                    );
                }
                self.apply_inline_assertion_at(site, actual)
            }
            Read::SelfValue => self.apply_inline_assertion_at(site, environment.self_type.clone()),
            Read::Numbered(number) => {
                self.apply_inline_assertion_at(site, environment.get(&format!("_{number}")))
            }
            Read::It => self.apply_inline_assertion_at(site, environment.get("it")),
            Read::BackReference(_) => self.apply_inline_assertion_at(site, Type::Any),
        }
    }

    /// Apply the common flow refinements for a CFG branch from owned HIR.
    ///
    /// This intentionally covers only facts represented by HIR operands and
    /// the already-computed environment. More elaborate parser predicates
    /// remain on the recursive adapter until their operand contracts are
    /// represented in HIR as well.
    pub(super) fn narrow_cfg_predicate(
        &mut self,
        expression: hir::ExprId,
        environment: &mut Environment,
        truthy: bool,
    ) {
        let Some(kind) = self
            .hir_program
            .expression(expression)
            .map(|expression| expression.kind.clone())
        else {
            return;
        };
        match kind {
            hir::ExprKind::Read(Read::Local(local)) => {
                self.narrow_cfg_local(local, environment, truthy)
            }
            hir::ExprKind::Read(Read::InstanceVariable(name)) => {
                let name = name.as_str().to_owned();
                let current = self.ivar_type(environment, &name);
                let narrowed = if truthy {
                    current.meet(&current.truthy_part())
                } else {
                    current.meet(&current.falsy_part())
                };
                environment.bind(ivar_refinement_key(&name), narrowed);
            }
            hir::ExprKind::Call(call) => {
                if call.name.as_str() == "!" {
                    if let hir::Receiver::Explicit(receiver) = call.receiver {
                        self.narrow_cfg_predicate(receiver, environment, !truthy);
                    }
                    return;
                }
                let argument_id = match call.arguments.first() {
                    None => None,
                    Some(hir::Argument::Positional(value)) => Some(*value),
                    Some(_) => return,
                };
                match call.receiver {
                    hir::Receiver::Explicit(receiver) => {
                        let Some(receiver_kind) = self
                            .hir_program
                            .expression(receiver)
                            .map(|expression| expression.kind.clone())
                        else {
                            return;
                        };
                        match receiver_kind {
                            hir::ExprKind::Read(Read::Local(local)) => self.narrow_cfg_call_target(
                                local,
                                &call.name,
                                argument_id,
                                environment,
                                truthy,
                            ),
                            hir::ExprKind::Read(Read::InstanceVariable(name)) => self
                                .narrow_cfg_ivar_call_target(
                                    name.as_str(),
                                    &call.name,
                                    argument_id,
                                    environment,
                                    truthy,
                                ),
                            _ => {}
                        }
                    }
                    hir::Receiver::Implicit
                        if matches!(call.name.as_str(), "is_a?" | "kind_of?" | "instance_of?") =>
                    {
                        if let Some(argument_id) = argument_id {
                            let current = environment.self_type.clone();
                            let expected =
                                self.cfg_predicate_expected_type(argument_id, environment);
                            environment.self_type = if truthy {
                                self.meet_predicate_type(&current, &expected)
                            } else {
                                current.without(&expected)
                            };
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn narrow_cfg_local(&self, local: hir::LocalId, environment: &mut Environment, truthy: bool) {
        let Some(name) = self.hir_program.local_name(local).map(|name| name.as_str()) else {
            return;
        };
        if environment.is_inferred(name) {
            return;
        }
        let current = environment.get(name);
        let narrowed = if truthy {
            current.meet(&current.truthy_part())
        } else {
            current.meet(&current.falsy_part())
        };
        environment.bind(name.to_owned(), narrowed);
        environment.set_known_truthiness(name.to_owned(), truthy);
    }

    fn narrow_cfg_call_target(
        &mut self,
        local: hir::LocalId,
        name: &hir::Name,
        argument: Option<hir::ExprId>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        let Some(local_name) = self
            .hir_program
            .local_name(local)
            .map(|name| name.as_str().to_owned())
        else {
            return;
        };
        if environment.is_inferred(&local_name) {
            return;
        }
        let current = environment.get(&local_name);
        let argument_type = argument
            .map(|argument| self.cfg_predicate_argument_type(argument, environment))
            .unwrap_or(Type::Any);
        let narrowed = match name.as_str() {
            "nil?" if argument.is_none() => {
                if truthy {
                    current.meet(&Type::Nil)
                } else {
                    current.without(&Type::Nil)
                }
            }
            "is_a?" | "kind_of?" | "instance_of?" if argument.is_some() => {
                if truthy {
                    self.meet_predicate_type(&current, &argument_type)
                } else {
                    current.without(&argument_type)
                }
            }
            "==" | "equal?" | "eql?" if argument.is_some() => {
                if truthy {
                    current.meet(&argument_type)
                } else {
                    current.clone()
                }
            }
            "!=" if argument.is_some() && truthy => {
                if matches!(argument_type, Type::Nil | Type::True | Type::False) {
                    current.without(&argument_type)
                } else {
                    current.clone()
                }
            }
            "!=" if argument.is_some() => current.meet(&argument_type),
            "empty?" if argument.is_none() => {
                if matches!(current, Type::Array(_) | Type::Tuple(_)) {
                    environment.set_known_nonempty_array(&local_name, !truthy);
                }
                return;
            }
            _ => return,
        };
        environment.bind(local_name, narrowed);
    }

    fn narrow_cfg_ivar_call_target(
        &mut self,
        name: &str,
        method: &hir::Name,
        argument: Option<hir::ExprId>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        let current = self.ivar_type(environment, name);
        let argument_type = argument
            .map(|argument| self.cfg_predicate_argument_type(argument, environment))
            .unwrap_or(Type::Any);
        let narrowed = match method.as_str() {
            "nil?" if argument.is_none() => {
                if truthy {
                    current.meet(&Type::Nil)
                } else {
                    current.without(&Type::Nil)
                }
            }
            "is_a?" | "kind_of?" | "instance_of?" if argument.is_some() => {
                if truthy {
                    self.meet_predicate_type(&current, &argument_type)
                } else {
                    current.without(&argument_type)
                }
            }
            _ => return,
        };
        environment.bind(ivar_refinement_key(name), narrowed);
    }

    fn cfg_predicate_argument_type(
        &mut self,
        expression: hir::ExprId,
        environment: &Environment,
    ) -> Type {
        let Some(kind) = self
            .hir_program
            .expression(expression)
            .map(|expression| expression.kind.clone())
        else {
            return Type::Any;
        };
        match kind {
            hir::ExprKind::Literal(literal) => Self::cfg_literal_type(&literal),
            hir::ExprKind::Read(Read::Constant(path)) => {
                let type_ = self.constant_type(environment, path.as_str());
                Self::class_object_value_type(&type_).unwrap_or(type_)
            }
            hir::ExprKind::Read(Read::Local(local)) => self
                .hir_program
                .local_name(local)
                .map_or(Type::Any, |name| environment.get(name.as_str())),
            _ => Type::Any,
        }
    }

    fn cfg_predicate_expected_type(
        &mut self,
        expression: hir::ExprId,
        environment: &Environment,
    ) -> Type {
        self.cfg_predicate_argument_type(expression, environment)
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

    pub(super) fn record_cfg_fallback(
        &mut self,
        node: &Node<'_>,
        kind: &str,
        fallback: CfgFallbackKind,
    ) {
        self.cfg_transfer_fallbacks.record(fallback);
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
