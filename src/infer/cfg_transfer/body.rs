//! Owned CFG transfer for complete HIR bodies.

use super::super::cfg_state::{BlockState, BodyContext};
use super::super::{
    Analyzer, Environment, Eval, Flow, FlowKind, OutcomeTypes, OwnedCallInput, SourceSite,
};
use super::cfg_global_refinement_key;
use super::patterns::{case_pattern_is_type_test, narrow_pattern_value, pattern_source_place};
use super::preflight;
use crate::cfg;
use crate::hir::{self, Read};
use crate::types::Type;
use std::collections::{HashMap, HashSet};

pub(super) struct BodyTransfer<'analyzer, 'src> {
    pub(super) analyzer: &'analyzer mut Analyzer<'src>,
    pub(super) context: BodyContext,
    pub(super) fixed_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    pub(super) normal_type: Type,
    pub(super) abrupt: OutcomeTypes,
    pub(super) terminal_flow: Flow,
    pub(super) final_environment: Option<Environment>,
}

impl<'analyzer, 'src> BodyTransfer<'analyzer, 'src> {
    fn suppress_internal_assignment_record(&self, operation: &cfg::Operation) -> bool {
        let Some(expression) = operation.expression else {
            return false;
        };
        let Some(hir::Expr {
            kind: hir::ExprKind::Assign { operator, .. },
            ..
        }) = self.analyzer.program.hir_program.expression(expression)
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
            let closure = analyzer.program.hir_program.closure(closure_id)?;
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

    fn transfer_array(
        analyzer: &mut Analyzer<'src>,
        site: SourceSite,
        elements: &[cfg::ArrayOperand],
        values: &[Option<Type>],
        preserve_fixed_shape: bool,
        defer_inline_assertion: bool,
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
        Some(if defer_inline_assertion {
            inferred
        } else {
            analyzer.apply_inline_assertion_in_environment_at(site, inferred, environment)
        })
    }

    fn transfer_hash(
        analyzer: &mut Analyzer<'src>,
        site: SourceSite,
        elements: &[cfg::HashOperand],
        values: &[Option<Type>],
        defer_inline_assertion: bool,
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
        let inferred = Type::Hash(Box::new(key), Box::new(value));
        Some(if defer_inline_assertion {
            inferred
        } else {
            analyzer.apply_inline_assertion_in_environment_at(site, inferred, environment)
        })
    }

    fn pattern_reachability(
        &self,
        pattern: &cfg::Pattern,
        source: &Type,
        state: &BlockState,
    ) -> Option<(bool, bool, Type)> {
        let (truthy, falsy) = match pattern {
            cfg::Pattern::Truthy | cfg::Pattern::LogicalAnd | cfg::Pattern::LogicalOr => (
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

    fn suppress_internal_call_record(&self, operation: &cfg::Operation) -> bool {
        // The parser-backed evaluator uses `!value` as a control-flow
        // predicate, so the source span remains associated with the operand
        // rather than gaining a second recorded type for Ruby's boolean
        // protocol call.  Keep the owned transfer's boolean result for branch
        // narrowing, but preserve the same observable type recording.
        let cfg::OperationKind::Call { name, .. } = &operation.kind else {
            return false;
        };
        if name.as_str() == "!" {
            return true;
        }
        let Some(expression) = operation
            .expression
            .and_then(|id| self.analyzer.program.hir_program.expression(id))
        else {
            return false;
        };
        let operator = match &expression.kind {
            hir::ExprKind::Assign { operator, .. } => operator,
            _ => return false,
        };
        if matches!(operator, hir::AssignOperator::And | hir::AssignOperator::Or) {
            // Logical writes also have an internal getter at the assignment
            // span. Its nilable result is not the value of `||=`/`&&=`.
            return !name.as_str().ends_with('=');
        }
        let hir::AssignOperator::Binary(operator) = operator else {
            return false;
        };
        // A compound assignment has internal getter, operator, and setter
        // calls at one source span. The getter's nilable type must not join
        // into the published assignment type; Ruby only reaches the binary
        // operator on its normal, non-nil receiver path.
        name.as_str() != operator.as_str() && !name.as_str().ends_with('=')
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
            .and_then(|condition| self.analyzer.program.hir_program.expression(condition))
            .map(|expression| &expression.kind)
        {
            let Some(name) = self.analyzer.program.hir_program.local_name(*local) else {
                return Self::truthiness_reachability(source);
            };
            if state.environment.is_inferred(name.as_str()) {
                return (true, true);
            }
        }
        Self::truthiness_reachability(source)
    }

    fn return_is_non_local(&self) -> bool {
        matches!(self.context.closure_kind, Some(hir::ClosureKind::Block))
    }

    fn finish_outcome(&mut self, kind: FlowKind, type_: Type, environment: Environment) {
        if kind == FlowKind::Return && !self.return_is_non_local() {
            self.normal_type = if self.normal_type.is_never() {
                type_
            } else {
                self.normal_type.join(&type_)
            };
            self.final_environment = Some(match self.final_environment.take() {
                Some(current) => current.join(&environment),
                None => environment,
            });
            return;
        }
        self.abrupt = self.abrupt.join(&OutcomeTypes::for_kind(kind, type_));
        self.terminal_flow = self.terminal_flow.union(Flow::abrupt(kind));
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

    pub(in crate::infer) fn eval_cfg_body_owned(
        &mut self,
        body_site: SourceSite,
        body_id: hir::BodyId,
        environment: &mut Environment,
        record_result: bool,
    ) -> Option<Eval> {
        if !preflight::body_can_transfer(&self.program.hir_program, body_id) {
            self.record_cfg_fallback_at(
                body_site,
                "body",
                super::CfgFallbackKind::UnsupportedOperation,
            );
            return None;
        }
        // The graph is syntax-only and immutable. It is lowered once when the
        // analyzer is created, then reused across seed, fixpoint, and final
        // passes instead of rebuilding the same body for every method visit.
        let graph_store = self.program.cfg_graphs.as_ref()?.clone();
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
                        | cfg::OperationKind::SetOutcome { .. }
                        | cfg::OperationKind::PatternTest { .. }
                        | cfg::OperationKind::BindForTarget { .. }
                )
            })
        }) {
            self.record_cfg_fallback_at(
                body_site,
                "operation",
                super::CfgFallbackKind::UnsupportedOperation,
            );
            return None;
        }

        let body = self.program.hir_program.body(body_id)?;
        let closure_kind = match &body.owner {
            hir::BodyOwner::Closure(closure) => self
                .program
                .hir_program
                .closure(*closure)
                .map(|closure| closure.kind),
            _ => None,
        };
        let context = BodyContext {
            body: body_id,
            method: environment.method_key.clone(),
            self_type: environment.self_type.clone(),
            parameters: body.parameters.clone(),
            strictness: self.strictness_at(body.span.start as usize),
            closure_kind,
        };
        let mut initial_environment = environment.clone();
        self.seed_cfg_global_state(&graph, &mut initial_environment);
        let fallback_environment = initial_environment.clone();
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
        let worklist = match cfg::transfer::run(&graph, &mut transfer, initial) {
            Ok(worklist) => worklist,
            Err(cfg::transfer::WorklistError::InvalidBlock(_)) => {
                transfer.analyzer.record_cfg_fallback_at(
                    body_site,
                    "edge",
                    super::CfgFallbackKind::UnsupportedEdge,
                );
                return None;
            }
            Err(cfg::transfer::WorklistError::Transfer(reason)) => {
                transfer.analyzer.record_cfg_fallback_detail_at(
                    body_site,
                    "operation",
                    super::CfgFallbackKind::UnsupportedOperation,
                    Some(&reason),
                );
                return None;
            }
        };
        let normal_type = transfer.normal_type.clone();
        let abrupt = transfer.abrupt.clone();
        let terminal_flow = transfer.terminal_flow;
        let mut final_environment = transfer
            .final_environment
            .clone()
            .unwrap_or(fallback_environment);
        drop(worklist);
        drop(transfer);
        self.cfg_transfer_bodies = self.cfg_transfer_bodies.saturating_add(1);
        self.commit_cfg_global_state(&graph, &final_environment);
        Self::clear_cfg_global_state(&graph, &mut final_environment);
        *environment = final_environment;
        let normal_type = (!normal_type.is_never()).then_some(normal_type);
        let flow = if normal_type.is_some() {
            Flow::normal().union(terminal_flow)
        } else {
            terminal_flow
        };
        let mut result = Eval::from_parts(normal_type, abrupt, flow);
        if record_result {
            result.type_ = self.record_at(body_site, result.type_.clone(), false, None);
        }
        Some(result)
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
                cfg::OperationKind::Const { value } => {
                    let type_ = Analyzer::cfg_literal_type(value);
                    if operation.defer_inline_assertion {
                        type_
                    } else {
                        self.analyzer.apply_inline_assertion_at(site, type_)
                    }
                }
                cfg::OperationKind::Read { place } => {
                    let read = match place {
                        cfg::Place::Local(local) => Read::Local(*local),
                        cfg::Place::InstanceVariable(name) => Read::InstanceVariable(name.clone()),
                        cfg::Place::ClassVariable(name) => Read::ClassVariable(name.clone()),
                        cfg::Place::Global(name) => Read::Global(name.clone()),
                        cfg::Place::Constant(path) => Read::Constant(path.clone()),
                    };
                    if operation.defer_inline_assertion {
                        let previous = self.analyzer.defer_inline_assertions;
                        self.analyzer.defer_inline_assertions = true;
                        let type_ =
                            self.analyzer
                                .transfer_cfg_read_at(site, read, &mut next.environment);
                        self.analyzer.defer_inline_assertions = previous;
                        type_
                    } else {
                        self.analyzer
                            .transfer_cfg_read_at(site, read, &mut next.environment)
                    }
                }
                cfg::OperationKind::ReadSpecial { read } => {
                    if operation.defer_inline_assertion {
                        let previous = self.analyzer.defer_inline_assertions;
                        self.analyzer.defer_inline_assertions = true;
                        let type_ = self.analyzer.transfer_cfg_read_at(
                            site,
                            read.clone(),
                            &mut next.environment,
                        );
                        self.analyzer.defer_inline_assertions = previous;
                        type_
                    } else {
                        self.analyzer.transfer_cfg_read_at(
                            site,
                            read.clone(),
                            &mut next.environment,
                        )
                    }
                }
                cfg::OperationKind::Write {
                    place,
                    value,
                    logical,
                } => {
                    let actual = next
                        .value(*value)
                        .ok_or_else(|| format!("missing write operand {:?}", value))?;
                    super::assignment::transfer_write(
                        self.analyzer,
                        site,
                        place,
                        actual,
                        *logical,
                        &mut next.environment,
                    )
                }
                cfg::OperationKind::BindForTarget { collection, target } => {
                    let collection_type = next.value(*collection).ok_or_else(|| {
                        format!("missing for collection operand {:?}", collection)
                    })?;
                    let element_type = self.analyzer.array_element_type(&collection_type);
                    super::assignment::transfer_for_target(
                        self.analyzer,
                        site,
                        target,
                        element_type,
                        &mut next.environment,
                    )
                    .ok_or_else(|| format!("unsupported for target at {:?}", operation.span))?
                }
                cfg::OperationKind::Call { .. } => {
                    let result = super::calls::transfer_call(
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
                        let exception = result.abrupt.raise_type.clone();
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
                    let non_raise = result.abrupt.without(FlowKind::Raise);
                    if !non_raise.all().is_never() {
                        self.abrupt = self.abrupt.join(&non_raise);
                        self.terminal_flow = self.terminal_flow.union(non_raise.flow());
                    }
                    if !result.flow.contains(FlowKind::Normal) {
                        self.analyzer.record_at(
                            site,
                            result.type_.clone(),
                            self.analyzer.reporting.report,
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
                    operation.defer_inline_assertion,
                    &mut next.environment,
                )
                .ok_or_else(|| format!("array transfer failed at {:?}", operation.span))?,
                cfg::OperationKind::BuildHash { elements } => Self::transfer_hash(
                    self.analyzer,
                    site,
                    elements,
                    &next.values,
                    operation.defer_inline_assertion,
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
                cfg::OperationKind::SetOutcome { kind, value } => {
                    let type_ = next
                        .value(*value)
                        .ok_or_else(|| format!("missing outcome operand {:?}", value))?;
                    let kind = match kind {
                        cfg::OutcomeKind::Return => FlowKind::Return,
                        cfg::OutcomeKind::Break => FlowKind::Break,
                        cfg::OutcomeKind::Next => FlowKind::Next,
                        cfg::OutcomeKind::Retry => FlowKind::Retry,
                    };
                    next.set_pending_outcome(kind, type_.clone());
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
                && !self.suppress_internal_call_record(operation)
                && !matches!(
                    operation.kind,
                    cfg::OperationKind::PatternTest { .. }
                        | cfg::OperationKind::Record { .. }
                        | cfg::OperationKind::SetOutcome { .. }
                        | cfg::OperationKind::BindForTarget { .. }
                )
            {
                if matches!(operation.kind, cfg::OperationKind::Call { .. }) {
                    self.analyzer
                        .record_at(site, type_, self.analyzer.reporting.report, None);
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
                // The CFG's terminal `Return` is ordinary completion of the
                // body. An explicit Ruby `return` is lowered to a pending
                // outcome and reaches `finish_outcome` through an unreachable
                // block, where block closures correctly preserve its
                // non-local behavior.
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
            cfg::Terminator::NonLocalReturn(value) => {
                let return_type = value
                    .and_then(|value| next.value(value))
                    .unwrap_or(Type::Nil);
                self.finish_outcome(FlowKind::Return, return_type, next.environment);
                Ok(Vec::new())
            }
            cfg::Terminator::Unreachable => {
                for (kind, type_) in [
                    (FlowKind::Return, next.pending_outcomes.return_type.clone()),
                    (FlowKind::Break, next.pending_outcomes.break_type.clone()),
                    (FlowKind::Next, next.pending_outcomes.next_type.clone()),
                    (FlowKind::Retry, next.pending_outcomes.retry_type.clone()),
                ] {
                    if !type_.is_never() {
                        self.finish_outcome(kind, type_, next.environment.clone());
                    }
                }
                Ok(Vec::new())
            }
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
                    if matches!(pattern, cfg::Pattern::LogicalOr)
                        && matches!(
                            source_place,
                            Some(
                                cfg::Place::Local(_)
                                    | cfg::Place::InstanceVariable(_)
                                    | cfg::Place::ClassVariable(_)
                                    | cfg::Place::Global(_)
                            )
                        )
                    {
                        // `||=` transfers always analyze their RHS in the
                        // legacy/Sorbet assignment protocol, including when
                        // the current value is already truthy.
                        (true, true)
                    } else {
                        (truthy, falsy)
                    }
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
                pending_target,
            } => {
                let target_block = graph
                    .block(*target)
                    .ok_or_else(|| format!("missing ensure target {:?}", target))?;
                let mut edges = Vec::new();
                if next.flow.contains(FlowKind::Normal)
                    && next.pending_exception.is_none()
                    && next.pending_outcomes.all().is_never()
                {
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
                        if let Some(expression) =
                            self.analyzer.program.hir_program.expression(*expression)
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
                if !next.pending_outcomes.all().is_never() {
                    for (kind, type_) in [
                        (FlowKind::Return, next.pending_outcomes.return_type.clone()),
                        (FlowKind::Break, next.pending_outcomes.break_type.clone()),
                        (FlowKind::Next, next.pending_outcomes.next_type.clone()),
                        (FlowKind::Retry, next.pending_outcomes.retry_type.clone()),
                    ] {
                        if type_.is_never() {
                            continue;
                        }
                        if let Some(pending_target) = pending_target {
                            let target_block = graph.block(*pending_target).ok_or_else(|| {
                                format!("missing pending ensure target {:?}", pending_target)
                            })?;
                            let mut pending = next.clone();
                            if let Some(parameter) = target_block.parameters.first() {
                                pending.set_value(parameter.value, type_);
                            }
                            pending.flow = Flow::normal();
                            edges.push(edge(*pending_target, pending));
                        } else {
                            self.finish_outcome(kind, type_, next.environment.clone());
                        }
                    }
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
