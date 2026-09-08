use super::cfg_state::{BlockState, BodyContext};
use super::{
    ivar_refinement_key, Analyzer, Environment, Eval, Flow, FlowKind, HirCallView, OutcomeTypes,
    OwnedCallInput, SharedKey, SourceSite, UntypedOrigin,
};
use crate::cfg;
use crate::hir::{self, ArrayElement, ExprKind, HashElement, Literal, Read};
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::{HashMap, HashSet};

mod legacy;
mod patterns;
mod preflight;

use patterns::{case_pattern_is_type_test, narrow_pattern_value, pattern_source_place};

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

struct BodyTransfer<'analyzer, 'src> {
    analyzer: &'analyzer mut Analyzer<'src>,
    context: BodyContext,
    fixed_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    normal_type: Type,
    abrupt: OutcomeTypes,
    terminal_flow: Flow,
    final_environment: Option<Environment>,
}

impl<'analyzer, 'src> BodyTransfer<'analyzer, 'src> {
    fn suppress_internal_assignment_record(&self, operation: &cfg::Operation) -> bool {
        let Some(expression) = operation.expression else {
            return false;
        };
        let Some(hir::Expr {
            kind: hir::ExprKind::Assign { operator, .. },
            ..
        }) = self.analyzer.hir_program.expression(expression)
        else {
            return false;
        };
        matches!(operator, hir::AssignOperator::And | hir::AssignOperator::Or)
            && matches!(
                operation.kind,
                cfg::OperationKind::Read { .. } | cfg::OperationKind::Write { .. }
            )
    }

    fn transfer_closure(
        analyzer: &mut Analyzer<'src>,
        closure_id: hir::ClosureId,
        outer: &Environment,
    ) -> Option<Type> {
        let (body_id, parameters, span) = {
            let closure = analyzer.hir_program.closure(closure_id)?;
            (closure.body, closure.parameters.clone(), closure.span)
        };
        let signature = Analyzer::inferred_hir_block_signature(&parameters);
        let mut closure_environment = outer.clone();
        let mut positional_index = 0;
        for parameter in &parameters.parameters {
            let type_ = match parameter.kind {
                hir::ParameterKind::Required
                | hir::ParameterKind::Optional
                | hir::ParameterKind::Post => {
                    let type_ = signature
                        .params
                        .get(positional_index)
                        .cloned()
                        .unwrap_or(Type::Any);
                    positional_index += 1;
                    type_
                }
                hir::ParameterKind::Rest | hir::ParameterKind::Forwarded => {
                    let type_ = signature
                        .params
                        .get(positional_index)
                        .cloned()
                        .unwrap_or(Type::Any);
                    positional_index += 1;
                    Type::Array(Box::new(type_))
                }
                hir::ParameterKind::RequiredKeyword | hir::ParameterKind::OptionalKeyword => {
                    Type::Any
                }
                hir::ParameterKind::KeywordRest => {
                    Type::Hash(Box::new(Type::Symbol), Box::new(Type::Any))
                }
                hir::ParameterKind::Block => Type::Proc(Vec::new(), Box::new(Type::Any)),
                hir::ParameterKind::Anonymous => Type::Any,
            };
            if let Some(name) = &parameter.name {
                closure_environment.bind(name.as_str().to_owned(), type_.clone());
            }
            if positional_index == 1 && parameter.name.is_none() {
                closure_environment.bind("it", type_);
            }
        }
        let body_result = analyzer.eval_cfg_body_owned(
            SourceSite::from_span(span, None),
            body_id,
            &mut closure_environment,
            false,
        )?;
        Some(Type::Proc(signature.params, Box::new(body_result.type_)))
    }

    fn transfer_write(
        analyzer: &mut Analyzer<'src>,
        site: SourceSite,
        place: &cfg::Place,
        actual: Type,
        environment: &mut Environment,
    ) -> Type {
        match place {
            cfg::Place::Local(local) => {
                let name = analyzer
                    .hir_program
                    .local_name(*local)
                    .map_or_else(String::new, |name| name.as_str().to_owned());
                let type_ =
                    analyzer.apply_inline_assertion_in_environment_at(site, actual, environment);
                environment.bind(name, type_.clone());
                type_
            }
            cfg::Place::InstanceVariable(name) => {
                let name = name.as_str().to_owned();
                let type_ =
                    analyzer.apply_inline_assertion_in_environment_at(site, actual, environment);
                analyzer.observe_ivar(environment, name.clone(), &type_, false);
                environment.bind(ivar_refinement_key(&name), type_.clone());
                type_
            }
            cfg::Place::ClassVariable(name) => {
                let type_ = analyzer.apply_inline_assertion_at(site, actual);
                analyzer.observe_class_var(environment, name.as_str().to_owned(), &type_);
                type_
            }
            cfg::Place::Global(name) => {
                let type_ = analyzer.apply_inline_assertion_at(site, actual);
                environment.bind(cfg_global_refinement_key(name.as_str()), type_.clone());
                type_
            }
            cfg::Place::Constant(path) => {
                let type_ = analyzer.apply_inline_assertion_at(site, actual);
                analyzer.observe_constant(environment, path.as_str().to_owned(), &type_);
                type_
            }
        }
    }

    fn transfer_for_target(
        analyzer: &mut Analyzer<'src>,
        site: SourceSite,
        target: &hir::AssignTarget,
        element_type: Type,
        environment: &mut Environment,
    ) -> Option<Type> {
        let place = match target {
            hir::AssignTarget::Local(local) => cfg::Place::Local(*local),
            hir::AssignTarget::InstanceVariable(name) => cfg::Place::InstanceVariable(name.clone()),
            hir::AssignTarget::ClassVariable(name) => cfg::Place::ClassVariable(name.clone()),
            hir::AssignTarget::Global(name) => cfg::Place::Global(name.clone()),
            hir::AssignTarget::Constant(path) => cfg::Place::Constant(path.clone()),
            hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. } => return None,
        };
        Some(Self::transfer_write(
            analyzer,
            site,
            &place,
            element_type,
            environment,
        ))
    }

    fn transfer_call(
        analyzer: &mut Analyzer<'src>,
        input: OwnedCallInput,
        values: &[Option<Type>],
        fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let call = input
            .expression
            .and_then(|expression| analyzer.hir_program.expression(expression))
            .and_then(|expression| match &expression.kind {
                hir::ExprKind::Call(call) => Some(call.clone()),
                _ => None,
            });
        let call_arguments = if let Some(call) = call {
            analyzer
                .cfg_owned_hir_call_arguments(
                    &input,
                    &call,
                    values,
                    fixed_array_elements,
                    environment,
                )?
                .into_call_arguments()
        } else {
            analyzer.cfg_owned_call_arguments(&input, values, fixed_array_elements)?
        };
        let receiver_type = match &input.receiver {
            cfg::ReceiverOperand::Implicit => environment.self_type.clone(),
            cfg::ReceiverOperand::Value(value) => {
                values.get(value.0 as usize).cloned().flatten()?
            }
            cfg::ReceiverOperand::Super | cfg::ReceiverOperand::Yield => {
                environment.self_type.clone()
            }
        };
        let has_block = input.block.is_some();
        let (type_, untyped_origin) = if matches!(input.receiver, cfg::ReceiverOperand::Yield) {
            let type_ = analyzer.cfg_yield_result(input.site, &call_arguments, environment)?;
            (type_, UntypedOrigin::Propagated)
        } else if matches!(input.receiver, cfg::ReceiverOperand::Super) {
            let key = analyzer.super_method_key(environment.method_key.as_ref()?)?;
            analyzer.record_method_dependency(&key, environment);
            if let Some(signature) = analyzer
                .observe_call(&key, &call_arguments, has_block)
                .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
            {
                let block_return_type = analyzer.cfg_block_return_type(
                    &input,
                    None,
                    &key,
                    &signature,
                    &call_arguments,
                    &receiver_type,
                    values,
                    environment,
                );
                let type_ = analyzer.invoke_signature_at(
                    input.site,
                    input.name.as_str(),
                    &signature,
                    &call_arguments,
                    Some(&receiver_type),
                    block_return_type.as_ref(),
                );
                let origin = analyzer
                    .resolve_method_key(&key)
                    .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                    .is_some_and(|state| state.explicit)
                    .then_some(UntypedOrigin::DeclaredSignature)
                    .unwrap_or(UntypedOrigin::InferredMethod);
                (type_, origin)
            } else {
                (Type::Any, UntypedOrigin::FallbackCall)
            }
        } else if matches!(input.receiver, cfg::ReceiverOperand::Implicit) {
            let key = analyzer.implicit_method_key(input.name.as_str(), environment);
            analyzer.record_method_dependency(&key, environment);
            if let Some(signature) = analyzer
                .observe_call(&key, &call_arguments, has_block)
                .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
            {
                let block_return_type = analyzer.cfg_block_return_type(
                    &input,
                    None,
                    &key,
                    &signature,
                    &call_arguments,
                    &receiver_type,
                    values,
                    environment,
                );
                let type_ = analyzer.invoke_signature_at(
                    input.site,
                    input.name.as_str(),
                    &signature,
                    &call_arguments,
                    Some(&receiver_type),
                    block_return_type.as_ref(),
                );
                let origin = analyzer
                    .resolve_method_key(&key)
                    .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                    .is_some_and(|state| state.explicit)
                    .then_some(UntypedOrigin::DeclaredSignature)
                    .unwrap_or(UntypedOrigin::InferredMethod);
                (type_, origin)
            } else {
                return None;
            }
        } else {
            let dispatch_receiver = if input.safe_navigation {
                receiver_type.without(&Type::Nil)
            } else {
                receiver_type.clone()
            };
            if input.safe_navigation
                && !receiver_type.is_any()
                && !receiver_type.is_never()
                && receiver_type.without(&Type::Nil) == receiver_type
            {
                analyzer.error_at(
                    input.site,
                    format!("Used `&.` operator on `{receiver_type}`, which can never be nil"),
                );
            }
            if input.safe_navigation && dispatch_receiver.is_never() {
                (Type::Nil, UntypedOrigin::FallbackCall)
            } else {
                let key = analyzer.receiver_method_key(
                    None,
                    &dispatch_receiver,
                    input.name.as_str(),
                    environment,
                );
                if let Some(key) = key {
                    analyzer.record_method_dependency(&key, environment);
                    if let Some(signature) = analyzer
                        .observe_call(&key, &call_arguments, has_block)
                        .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
                    {
                        let block_return_type = analyzer.cfg_block_return_type(
                            &input,
                            None,
                            &key,
                            &signature,
                            &call_arguments,
                            &dispatch_receiver,
                            values,
                            environment,
                        );
                        let type_ = analyzer.invoke_signature_at(
                            input.site,
                            input.name.as_str(),
                            &signature,
                            &call_arguments,
                            Some(&dispatch_receiver),
                            block_return_type.as_ref(),
                        );
                        let type_ = if input.name.as_str() == "new"
                            && Analyzer::class_object_instance_type(&dispatch_receiver).is_some()
                        {
                            analyzer.instantiate_generic_class(type_)
                        } else {
                            type_
                        };
                        let origin = analyzer
                            .resolve_method_key(&key)
                            .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                            .is_some_and(|state| state.explicit)
                            .then_some(UntypedOrigin::DeclaredSignature)
                            .unwrap_or(UntypedOrigin::InferredMethod);
                        (type_, origin)
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
        };
        let type_ = if input.safe_navigation && !receiver_type.is_any() {
            Type::union([Type::Nil, type_])
        } else {
            type_
        };
        analyzer.remember_untyped_origin_at(input.site, &type_, untyped_origin);
        let mut result = if type_.is_never() {
            Eval::raised(type_)
        } else {
            Eval::value(type_)
        };
        let type_ = analyzer.apply_inline_assertion_in_environment_at(
            input.site,
            result.type_.clone(),
            environment,
        );
        if result.normal_type.is_some() {
            result.normal_type = Some(type_.clone());
        }
        result.type_ = type_;
        Some(result)
    }

    fn transfer_array(
        analyzer: &mut Analyzer<'src>,
        site: SourceSite,
        elements: &[cfg::ArrayOperand],
        values: &[Option<Type>],
        preserve_fixed_shape: bool,
        environment: &mut Environment,
    ) -> Option<Type> {
        let mut element_types = Vec::with_capacity(elements.len());
        let mut fixed_length = true;
        let mut element = Type::Never;
        for operand in elements {
            let (value, splat_span) = match operand {
                cfg::ArrayOperand::Value(value) => (value, None),
                cfg::ArrayOperand::Splat { value, span } => (value, Some(*span)),
            };
            let type_ = values.get(value.0 as usize).cloned().flatten()?;
            let type_ = if let Some(span) = splat_span {
                fixed_length = false;
                let element_type = analyzer.array_element_type(&type_);
                analyzer.record_at(
                    SourceSite::from_span(span, None),
                    type_.clone(),
                    false,
                    None,
                );
                element_type
            } else {
                type_
            };
            element_types.push(type_.clone());
            element = element.join(&type_);
        }
        let element = if element.is_never() {
            if analyzer.preserve_literal_tuples {
                Type::Never
            } else {
                Type::Any
            }
        } else {
            element
        };
        let inferred = if fixed_length
            && (preserve_fixed_shape
                || (analyzer.preserve_literal_tuples && analyzer.literal_tuple_depth == 0)
                || analyzer.expected_return_type.as_ref().is_some_and(|expected| {
                    matches!(expected, Type::Tuple(expected) if expected.len() == element_types.len())
                }))
        {
            Type::Tuple(element_types)
        } else {
            Type::Array(Box::new(element))
        };
        Some(analyzer.apply_inline_assertion_in_environment_at(site, inferred, environment))
    }

    fn transfer_hash(
        analyzer: &mut Analyzer<'src>,
        site: SourceSite,
        elements: &[cfg::HashOperand],
        values: &[Option<Type>],
        environment: &mut Environment,
    ) -> Option<Type> {
        let mut key = Type::Never;
        let mut value = Type::Never;
        for element in elements {
            match element {
                cfg::HashOperand::Pair {
                    key: key_id,
                    value: value_id,
                } => {
                    key = key.join(&values.get(key_id.0 as usize).cloned().flatten()?);
                    value = value.join(&values.get(value_id.0 as usize).cloned().flatten()?);
                }
                cfg::HashOperand::Splat {
                    value: value_id, ..
                } => match values.get(value_id.0 as usize).cloned().flatten()? {
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
        Some(analyzer.apply_inline_assertion_in_environment_at(
            site,
            Type::Hash(Box::new(key), Box::new(value)),
            environment,
        ))
    }

    fn pattern_reachability(
        &self,
        pattern: &cfg::Pattern,
        source: &Type,
        state: &BlockState,
    ) -> Option<(bool, bool, Type)> {
        let (truthy, falsy) = match pattern {
            cfg::Pattern::Truthy => (
                !source.truthy_part().is_never(),
                !source.falsy_part().is_never(),
            ),
            cfg::Pattern::Nil => (
                !source.meet(&Type::Nil).is_never(),
                !source.without(&Type::Nil).is_never(),
            ),
            cfg::Pattern::Iteration => (true, true),
            cfg::Pattern::Case {
                condition: condition_id,
                expression,
            } => {
                let condition = state.value(*condition_id).unwrap_or(Type::Any);
                let is_type_test =
                    case_pattern_is_type_test(self.analyzer, *expression, &condition);
                let expected = Analyzer::class_object_value_type(&condition).unwrap_or(condition);
                self.case_match_reachability(source, &expected, is_type_test)
            }
        };
        let test_type = match (truthy, falsy) {
            (true, true) => Type::union([Type::True, Type::False]),
            (true, false) => Type::True,
            (false, true) => Type::False,
            (false, false) => Type::Never,
        };
        Some((truthy, falsy, test_type))
    }

    fn case_match_reachability(
        &self,
        source: &Type,
        expected: &Type,
        is_type_test: bool,
    ) -> (bool, bool) {
        if source.is_any() || expected.is_any() {
            return (true, true);
        }
        if let Type::Union(members) = source {
            return members
                .iter()
                .fold((false, false), |(truthy, falsy), member| {
                    let (member_truthy, member_falsy) =
                        self.case_match_reachability(member, expected, is_type_test);
                    (truthy || member_truthy, falsy || member_falsy)
                });
        }
        if !is_type_test {
            return (
                !self
                    .analyzer
                    .definitely_disjoint_class_types(source, expected),
                true,
            );
        }
        if self.analyzer.is_assignable(source, expected) {
            (true, false)
        } else if self.analyzer.is_assignable(expected, source)
            || !self
                .analyzer
                .definitely_disjoint_class_types(source, expected)
        {
            (true, true)
        } else {
            (false, true)
        }
    }

    fn truthiness_reachability(source: &Type) -> (bool, bool) {
        (
            !source.truthy_part().is_never(),
            !source.falsy_part().is_never(),
        )
    }

    fn narrow_conditional_branch(
        &mut self,
        graph: &cfg::Cfg,
        block: cfg::BlockId,
        truthy: bool,
        environment: &mut Environment,
    ) {
        let Some(conditional) = graph.conditionals.iter().find(|conditional| {
            (truthy && conditional.truthy == block) || (!truthy && conditional.falsy == block)
        }) else {
            return;
        };
        self.analyzer
            .narrow_cfg_predicate(conditional.condition, environment, truthy);
    }

    fn exception_edge(
        &self,
        graph: &cfg::Cfg,
        block: &cfg::BasicBlock,
        mut state: BlockState,
        exception: Type,
    ) -> Option<cfg::transfer::TransferEdge<BlockState>> {
        let target = block.unwind?;
        let target_block = graph.block(target)?;
        if let Some(parameter) = target_block.parameters.first() {
            state.set_value(parameter.value, exception.clone());
        }
        state.route_exception(exception);
        Some(cfg::transfer::TransferEdge { target, state })
    }

    fn is_rescue_entry(graph: &cfg::Cfg, block: cfg::BlockId) -> bool {
        graph
            .blocks
            .iter()
            .any(|candidate| candidate.unwind == Some(block))
    }

    fn conditional_reachability(
        &self,
        graph: &cfg::Cfg,
        truthy: cfg::BlockId,
        falsy: cfg::BlockId,
        source: &Type,
        state: &BlockState,
    ) -> (bool, bool) {
        let condition = graph
            .conditionals
            .iter()
            .find(|conditional| conditional.truthy == truthy && conditional.falsy == falsy)
            .map(|conditional| conditional.condition);
        if let Some(hir::ExprKind::Read(Read::Local(local))) = condition
            .and_then(|condition| self.analyzer.hir_program.expression(condition))
            .map(|expression| &expression.kind)
        {
            let Some(name) = self.analyzer.hir_program.local_name(*local) else {
                return Self::truthiness_reachability(source);
            };
            if state.environment.is_inferred(name.as_str()) {
                return (true, true);
            }
        }
        Self::truthiness_reachability(source)
    }
}

impl<'analyzer, 'src> cfg::transfer::BlockTransfer for BodyTransfer<'analyzer, 'src> {
    type State = BlockState;
    type Error = String;

    fn transfer_block(
        &mut self,
        graph: &cfg::Cfg,
        block: &cfg::BasicBlock,
        state: &Self::State,
    ) -> Result<Vec<cfg::transfer::TransferEdge<Self::State>>, Self::Error> {
        debug_assert_eq!(graph.body, self.context.body);
        let _strictness = self.context.strictness;
        let mut next = state.clone();
        let mut exception_edges = Vec::new();
        for operation in &block.operations {
            let site = SourceSite::from_span(operation.span, operation.expression);
            let type_ = match &operation.kind {
                cfg::OperationKind::Const { value } => self
                    .analyzer
                    .apply_inline_assertion_at(site, Analyzer::cfg_literal_type(value)),
                cfg::OperationKind::Read { place } => {
                    let read = match place {
                        cfg::Place::Local(local) => Read::Local(*local),
                        cfg::Place::InstanceVariable(name) => Read::InstanceVariable(name.clone()),
                        cfg::Place::ClassVariable(name) => Read::ClassVariable(name.clone()),
                        cfg::Place::Global(name) => Read::Global(name.clone()),
                        cfg::Place::Constant(path) => Read::Constant(path.clone()),
                    };
                    self.analyzer
                        .transfer_cfg_read_at(site, read, &mut next.environment)
                }
                cfg::OperationKind::ReadSpecial { read } => {
                    self.analyzer
                        .transfer_cfg_read_at(site, read.clone(), &mut next.environment)
                }
                cfg::OperationKind::Write { place, value } => {
                    let actual = next
                        .value(*value)
                        .ok_or_else(|| format!("missing write operand {:?}", value))?;
                    Self::transfer_write(self.analyzer, site, place, actual, &mut next.environment)
                }
                cfg::OperationKind::BindForTarget { collection, target } => {
                    let collection_type = next.value(*collection).ok_or_else(|| {
                        format!("missing for collection operand {:?}", collection)
                    })?;
                    let element_type = self.analyzer.array_element_type(&collection_type);
                    Self::transfer_for_target(
                        self.analyzer,
                        site,
                        target,
                        element_type,
                        &mut next.environment,
                    )
                    .ok_or_else(|| format!("unsupported for target at {:?}", operation.span))?
                }
                cfg::OperationKind::Call { .. } => {
                    let result = Self::transfer_call(
                        self.analyzer,
                        OwnedCallInput::from_operation(operation).ok_or_else(|| {
                            format!("missing owned call input at {:?}", operation.span)
                        })?,
                        &next.values,
                        &self.fixed_array_elements,
                        &mut next.environment,
                    )
                    .ok_or_else(|| format!("call transfer failed at {:?}", operation.span))?;
                    if result.flow.contains(FlowKind::Raise) {
                        let exception = if result.abrupt.raise_type.is_never() {
                            Type::named("StandardError")
                        } else {
                            result.abrupt.raise_type.clone()
                        };
                        if let Some(edge) =
                            self.exception_edge(graph, block, next.clone(), exception.clone())
                        {
                            exception_edges.push(edge);
                        } else {
                            self.abrupt = self
                                .abrupt
                                .join(&OutcomeTypes::for_kind(FlowKind::Raise, exception));
                            self.terminal_flow =
                                self.terminal_flow.union(Flow::abrupt(FlowKind::Raise));
                        }
                    }
                    if !result.flow.contains(FlowKind::Normal) {
                        self.analyzer.record_at(
                            site,
                            result.type_.clone(),
                            self.analyzer.report,
                            None,
                        );
                        return Ok(exception_edges);
                    }
                    result.normal_type.ok_or_else(|| {
                        format!("call has no normal result at {:?}", operation.span)
                    })?
                }
                cfg::OperationKind::BuildArray { elements } => Self::transfer_array(
                    self.analyzer,
                    site,
                    elements,
                    &next.values,
                    operation
                        .result
                        .is_some_and(|result| self.fixed_array_elements.contains_key(&result)),
                    &mut next.environment,
                )
                .ok_or_else(|| format!("array transfer failed at {:?}", operation.span))?,
                cfg::OperationKind::BuildHash { elements } => Self::transfer_hash(
                    self.analyzer,
                    site,
                    elements,
                    &next.values,
                    &mut next.environment,
                )
                .ok_or_else(|| format!("hash transfer failed at {:?}", operation.span))?,
                cfg::OperationKind::Record { value } => {
                    let type_ = value
                        .as_ref()
                        .and_then(|value| next.value(*value))
                        .unwrap_or(Type::Never);
                    self.analyzer.record_at(site, type_.clone(), false, None);
                    type_
                }
                cfg::OperationKind::PatternTest { value, pattern } => {
                    let source = next
                        .value(*value)
                        .ok_or_else(|| format!("missing pattern operand {:?}", value))?;
                    let (_, _, type_) = self
                        .pattern_reachability(pattern, &source, &next)
                        .ok_or_else(|| "unsupported pattern reachability".to_owned())?;
                    type_
                }
                cfg::OperationKind::MakeClosure { closure } => {
                    Self::transfer_closure(self.analyzer, *closure, &next.environment)
                        .ok_or_else(|| format!("closure transfer failed at {:?}", operation.span))?
                }
                _ => return Err(format!("unsupported CFG operation at {:?}", operation.span)),
            };
            if let Some(result) = operation.result {
                next.set_value(result, type_.clone());
            }
            if !self.suppress_internal_assignment_record(operation)
                && !matches!(
                    operation.kind,
                    cfg::OperationKind::PatternTest { .. }
                        | cfg::OperationKind::Record { .. }
                        | cfg::OperationKind::BindForTarget { .. }
                )
            {
                if matches!(operation.kind, cfg::OperationKind::Call { .. }) {
                    self.analyzer
                        .record_at(site, type_, self.analyzer.report, None);
                } else {
                    self.analyzer.record_at(site, type_, false, None);
                }
            }
        }

        let edge = |target, state| cfg::transfer::TransferEdge { target, state };
        match &block.terminator {
            cfg::Terminator::Jump { target, arguments } => {
                if next.pending_exception.is_some() && Self::is_rescue_entry(graph, block.id) {
                    next.handle_exception();
                }
                let target_block = graph
                    .block(*target)
                    .ok_or_else(|| format!("missing jump target {:?}", target))?;
                for (parameter, argument) in target_block.parameters.iter().zip(arguments) {
                    let type_ = next
                        .value(*argument)
                        .ok_or_else(|| format!("missing jump operand {:?}", argument))?;
                    next.set_value(parameter.value, type_);
                }
                Ok(vec![edge(*target, next)])
            }
            cfg::Terminator::Return(value) => {
                let return_type = value
                    .and_then(|value| next.value(value))
                    .unwrap_or(Type::Nil);
                self.normal_type = if self.normal_type.is_never() {
                    return_type
                } else {
                    self.normal_type.join(&return_type)
                };
                self.final_environment = Some(match self.final_environment.take() {
                    Some(environment) => environment.join(&next.environment),
                    None => next.environment,
                });
                self.terminal_flow = self.terminal_flow.union(next.flow);
                Ok(Vec::new())
            }
            cfg::Terminator::Unreachable => Ok(Vec::new()),
            cfg::Terminator::Branch {
                condition,
                truthy,
                falsy,
            } => {
                let pattern =
                    block
                        .operations
                        .iter()
                        .find_map(|operation| match operation.result {
                            Some(result) if result == *condition => {
                                if let cfg::OperationKind::PatternTest { value, pattern } =
                                    &operation.kind
                                {
                                    Some((Some(*value), Some(pattern)))
                                } else {
                                    Some((None, None))
                                }
                            }
                            _ => None,
                        });
                let (source_id, pattern) = pattern.unwrap_or((None, None));
                let source_place =
                    source_id.and_then(|source_id| pattern_source_place(graph, source_id));
                let source = next
                    .value(source_id.unwrap_or(*condition))
                    .ok_or_else(|| format!("missing branch operand {:?}", condition))?;
                let (truthy_reachable, falsy_reachable) = if let Some(pattern) = pattern {
                    let (truthy, falsy, _) = self
                        .pattern_reachability(pattern, &source, &next)
                        .ok_or_else(|| "unsupported pattern reachability".to_owned())?;
                    (truthy, falsy)
                } else {
                    self.conditional_reachability(graph, *truthy, *falsy, &source, &next)
                };
                let mut edges = Vec::with_capacity(2);
                if truthy_reachable {
                    let mut state = next.clone();
                    if pattern.is_none() {
                        self.narrow_conditional_branch(
                            graph,
                            *truthy,
                            true,
                            &mut state.environment,
                        );
                    } else if let Some(source_id) = source_id {
                        let pattern = pattern.expect("pattern was present");
                        narrow_pattern_value(
                            self.analyzer,
                            &mut state,
                            source_id,
                            pattern,
                            true,
                            source_place.as_ref(),
                        );
                        if state.pending_exception.is_some()
                            && matches!(pattern, cfg::Pattern::Case { .. })
                        {
                            state.handle_exception();
                        }
                    }
                    edges.push(edge(*truthy, state));
                }
                if falsy_reachable {
                    let mut state = next;
                    if pattern.is_none() {
                        self.narrow_conditional_branch(
                            graph,
                            *falsy,
                            false,
                            &mut state.environment,
                        );
                    } else if let Some(source_id) = source_id {
                        let pattern = pattern.expect("pattern was present");
                        narrow_pattern_value(
                            self.analyzer,
                            &mut state,
                            source_id,
                            pattern,
                            false,
                            source_place.as_ref(),
                        );
                    }
                    edges.push(edge(*falsy, state));
                }
                Ok(edges)
            }
            cfg::Terminator::Raise(value) => {
                let exception = next
                    .value(*value)
                    .unwrap_or_else(|| Type::named("StandardError"));
                if let Some(edge) = self.exception_edge(graph, block, next, exception.clone()) {
                    exception_edges.push(edge);
                } else {
                    self.abrupt = self
                        .abrupt
                        .join(&OutcomeTypes::for_kind(FlowKind::Raise, exception));
                    self.terminal_flow = self.terminal_flow.union(Flow::abrupt(FlowKind::Raise));
                }
                Ok(exception_edges)
            }
            cfg::Terminator::EnsureComplete {
                expression,
                target,
                arguments,
            } => {
                let target_block = graph
                    .block(*target)
                    .ok_or_else(|| format!("missing ensure target {:?}", target))?;
                let mut edges = Vec::new();
                if next.flow.contains(FlowKind::Normal) {
                    let mut normal = next.clone();
                    normal.pending_exception = None;
                    normal.flow = normal.flow.without(FlowKind::Raise);
                    for (parameter, argument) in target_block.parameters.iter().zip(arguments) {
                        let type_ = normal
                            .value(*argument)
                            .ok_or_else(|| format!("missing ensure operand {:?}", argument))?;
                        normal.set_value(parameter.value, type_);
                    }
                    if let Some(value) = arguments.first().and_then(|value| normal.value(*value)) {
                        if let Some(expression) = self.analyzer.hir_program.expression(*expression)
                        {
                            self.analyzer.record_at(
                                SourceSite::from_span(expression.span, None),
                                value,
                                false,
                                None,
                            );
                        }
                    }
                    edges.push(edge(*target, normal));
                }
                if next.flow.contains(FlowKind::Raise) {
                    if let Some(exception) = next.pending_exception.clone() {
                        if let Some(exception_edge) =
                            self.exception_edge(graph, block, next, exception.clone())
                        {
                            edges.push(exception_edge);
                        } else {
                            self.abrupt = self
                                .abrupt
                                .join(&OutcomeTypes::for_kind(FlowKind::Raise, exception));
                            self.terminal_flow =
                                self.terminal_flow.union(Flow::abrupt(FlowKind::Raise));
                        }
                    }
                }
                Ok(edges)
            }
        }
    }

    fn join_state(
        &mut self,
        current: Option<&Self::State>,
        incoming: Self::State,
    ) -> (Self::State, bool) {
        let Some(current) = current else {
            return (incoming, true);
        };
        let joined = current.join(&incoming);
        let changed = joined != *current;
        (joined, changed)
    }
}

impl<'src> Analyzer<'src> {
    fn seed_cfg_global_state(&self, graph: &cfg::Cfg, environment: &mut Environment) {
        for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
            let place = match &operation.kind {
                cfg::OperationKind::Read { place } | cfg::OperationKind::Write { place, .. } => {
                    place
                }
                _ => continue,
            };
            let cfg::Place::Global(name) = place else {
                continue;
            };
            let name = name.as_str();
            let type_ = self.globals.get(name).cloned().unwrap_or(Type::Any);
            environment.bind(cfg_global_refinement_key(name), type_);
        }
    }

    fn commit_cfg_global_state(&mut self, graph: &cfg::Cfg, environment: &Environment) {
        for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
            let place = match &operation.kind {
                cfg::OperationKind::Write { place, .. } => place,
                _ => continue,
            };
            let cfg::Place::Global(name) = place else {
                continue;
            };
            let name = name.as_str();
            if let Some(type_) = environment
                .contains(&cfg_global_refinement_key(name))
                .then(|| environment.get(&cfg_global_refinement_key(name)))
            {
                self.observe_global(name.to_owned(), &type_);
            }
        }
    }

    fn clear_cfg_global_state(graph: &cfg::Cfg, environment: &mut Environment) {
        for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
            let place = match &operation.kind {
                cfg::OperationKind::Read { place } | cfg::OperationKind::Write { place, .. } => {
                    place
                }
                _ => continue,
            };
            let cfg::Place::Global(name) = place else {
                continue;
            };
            environment.remove(&cfg_global_refinement_key(name.as_str()));
        }
    }

    /// Run the generic CFG transfer over a complete, straight-line method
    /// body. Bodies with dispatch, branches, or exceptional control flow stay
    /// on the recursive evaluator until their owned transfer exists; the
    /// preflight is important because a failed transfer must not leave partial
    /// diagnostics or recorded types behind.
    pub(super) fn eval_cfg_body<'node>(
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

    pub(super) fn eval_cfg_body_owned(
        &mut self,
        body_site: SourceSite,
        body_id: hir::BodyId,
        environment: &mut Environment,
        record_result: bool,
    ) -> Option<Eval> {
        if !preflight::body_can_transfer(&self.hir_program, body_id) {
            return None;
        }
        // The graph is syntax-only and immutable. It is lowered once when the
        // analyzer is created, then reused across seed, fixpoint, and final
        // passes instead of rebuilding the same body for every method visit.
        let graph_store = self.cfg_graphs.as_ref()?.clone();
        let graph = graph_store.get(body_id.0 as usize)?;
        let fixed_array_candidates = graph
            .blocks
            .iter()
            .flat_map(|block| block.operations.iter())
            .filter_map(|operation| {
                let result = operation.result?;
                let cfg::OperationKind::BuildArray { elements } = &operation.kind else {
                    return None;
                };
                let elements = elements
                    .iter()
                    .map(|element| match element {
                        cfg::ArrayOperand::Value(value) => Some(*value),
                        cfg::ArrayOperand::Splat { .. } => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some((result, elements))
            })
            .collect::<HashMap<_, _>>();
        let splatted_values = graph
            .blocks
            .iter()
            .flat_map(|block| block.operations.iter())
            .filter_map(|operation| match &operation.kind {
                cfg::OperationKind::Call { arguments, .. } => Some(arguments),
                _ => None,
            })
            .flat_map(|arguments| arguments.iter())
            .filter_map(|argument| match argument {
                cfg::ArgumentOperand::Splat(value) => Some(*value),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let fixed_array_elements = fixed_array_candidates
            .into_iter()
            .filter(|(value, _)| splatted_values.contains(value))
            .collect::<HashMap<_, _>>();
        if graph.blocks.iter().any(|block| {
            block.operations.iter().any(|operation| {
                !matches!(
                    operation.kind,
                    cfg::OperationKind::Const { .. }
                        | cfg::OperationKind::Read { .. }
                        | cfg::OperationKind::ReadSpecial { .. }
                        | cfg::OperationKind::Write { .. }
                        | cfg::OperationKind::Call { .. }
                        | cfg::OperationKind::MakeClosure { .. }
                        | cfg::OperationKind::BuildArray { .. }
                        | cfg::OperationKind::BuildHash { .. }
                        | cfg::OperationKind::Record { .. }
                        | cfg::OperationKind::PatternTest { .. }
                        | cfg::OperationKind::BindForTarget { .. }
                )
            })
        }) {
            return None;
        }

        let body = self.hir_program.body(body_id)?;
        let context = BodyContext {
            body: body_id,
            method: environment.method_key.clone(),
            self_type: environment.self_type.clone(),
            parameters: body.parameters.clone(),
            strictness: self.strictness_at(body.span.start as usize),
        };
        let mut initial_environment = environment.clone();
        self.seed_cfg_global_state(&graph, &mut initial_environment);
        let initial = BlockState::with_values(initial_environment, Vec::new(), Flow::normal());
        let mut transfer = BodyTransfer {
            analyzer: self,
            context,
            fixed_array_elements,
            normal_type: Type::Never,
            abrupt: OutcomeTypes::default(),
            terminal_flow: Flow::empty(),
            final_environment: None,
        };
        let worklist = cfg::transfer::run(&graph, &mut transfer, initial).ok()?;
        let normal_type = transfer.normal_type.clone();
        let abrupt = transfer.abrupt.clone();
        let terminal_flow = transfer.terminal_flow;
        let mut final_environment = transfer.final_environment.clone()?;
        drop(worklist);
        drop(transfer);
        self.cfg_transfer_bodies = self.cfg_transfer_bodies.saturating_add(1);
        self.commit_cfg_global_state(&graph, &final_environment);
        Self::clear_cfg_global_state(&graph, &mut final_environment);
        *environment = final_environment;
        let mut result = Eval::from_parts(
            Some(normal_type),
            abrupt,
            Flow::normal().union(terminal_flow),
        );
        if record_result {
            result.type_ = self.record_at(body_site, result.type_.clone(), false, None);
        }
        Some(result)
    }

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
