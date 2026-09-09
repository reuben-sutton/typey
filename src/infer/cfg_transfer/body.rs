//! Owned CFG transfer for complete HIR bodies.

use super::super::cfg_state::{BlockState, BodyContext};
use super::super::{
    Analyzer, Environment, Eval, Flow, FlowKind, OutcomeTypes, OwnedCallInput, SourceSite,
};
use super::globals::{clear_cfg_global_state, commit_cfg_global_state, seed_cfg_global_state};
use super::patterns::{narrow_pattern_value, pattern_source, pattern_source_place};
use super::preflight;
use crate::cfg;
use crate::hir::{self, Read};
use crate::types::Type;
use std::collections::HashMap;

pub(super) struct BodyTransfer<'analyzer, 'src> {
    pub(super) analyzer: &'analyzer mut Analyzer<'src>,
    pub(super) context: BodyContext,
    pub(super) fixed_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    pub(super) fixed_shape_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
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

    fn suppress_internal_call_record(&self, operation: &cfg::Operation) -> bool {
        // The parser-backed evaluator uses `!value` as a control-flow
        // predicate, so the source span remains associated with the operand
        // rather than gaining a second recorded type for Ruby's boolean
        // protocol call.  Keep the owned transfer's boolean result for branch
        // narrowing, but preserve the same observable type recording.
        let cfg::OperationKind::Call { name, .. } = &operation.kind else {
            return false;
        };
        if operation.defer_inline_assertion
            && self
                .analyzer
                .inline_assertion_for_site(crate::infer::SourceSite::from_span(
                    operation.span,
                    operation.expression,
                ))
                .is_some()
        {
            // Safe navigation lowers its real call on one branch and applies
            // the trailing assertion at the synthetic join. The branch call
            // must not publish a competing pre-assertion type for the same
            // source span.
            return true;
        }
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
    pub(in crate::infer) fn eval_cfg_body_owned(
        &mut self,
        body_site: SourceSite,
        body_id: hir::BodyId,
        environment: &mut Environment,
        record_result: bool,
    ) -> Option<Eval> {
        if let Some(failure) = preflight::body_transfer_failure(&self.program.hir_program, body_id)
        {
            self.record_cfg_fallback_detail_at(
                SourceSite::from_span(failure.span, None),
                "body",
                super::CfgFallbackKind::UnsupportedOperation,
                Some(failure.reason.as_str()),
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
                let cfg::OperationKind::BuildArray { elements, .. } = &operation.kind else {
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
        let fixed_array_elements = fixed_array_candidates.clone();
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
            .collect::<std::collections::HashSet<_>>();
        let fixed_shape_array_elements = fixed_array_candidates
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
                        | cfg::OperationKind::MultiWrite { .. }
                        | cfg::OperationKind::Defined { .. }
                        | cfg::OperationKind::Call { .. }
                        | cfg::OperationKind::MakeClosure { .. }
                        | cfg::OperationKind::BuildArray { .. }
                        | cfg::OperationKind::BuildHash { .. }
                        | cfg::OperationKind::BuildInterpolated { .. }
                        | cfg::OperationKind::BuildRange { .. }
                        | cfg::OperationKind::Definition { .. }
                        | cfg::OperationKind::Record { .. }
                        | cfg::OperationKind::ApplyAssertion { .. }
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
        let original_self_type = environment.self_type.clone();
        let mut initial_environment = environment.clone();
        if !self.defer_inline_assertions {
            if let Some(assertion) = self
                .inline_assertion_for_site(body_site)
                .filter(|assertion| assertion.kind == crate::signature::AssertionKind::SelfAs)
            {
                initial_environment.self_type = self.resolve_type_names(
                    &assertion.type_,
                    self.lexical_owner(&initial_environment).as_deref(),
                );
            }
        }
        seed_cfg_global_state(self, &graph, &mut initial_environment);
        let fallback_environment = initial_environment.clone();
        let initial = BlockState::with_values(initial_environment, Vec::new(), Flow::normal());
        let mut transfer = BodyTransfer {
            analyzer: self,
            context,
            fixed_array_elements,
            fixed_shape_array_elements,
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
        // `self as` narrows only this expression/body evaluation. Do not
        // publish the temporary receiver context to the enclosing method or
        // caller environment.
        final_environment.self_type = original_self_type;
        drop(worklist);
        drop(transfer);
        self.cfg_transfer_bodies = self.cfg_transfer_bodies.saturating_add(1);
        commit_cfg_global_state(self, &graph, &final_environment);
        clear_cfg_global_state(&graph, &mut final_environment);
        *environment = final_environment;
        let normal_type = (!normal_type.is_never()).then_some(normal_type);
        let flow = if normal_type.is_some() {
            Flow::normal().union(terminal_flow)
        } else {
            terminal_flow
        };
        let mut result = Eval::from_parts(normal_type, abrupt, flow);
        if record_result {
            let expression_type = if result.normal_type.is_some() {
                result.type_.clone()
            } else {
                Type::Never
            };
            result.type_ = self.record_at(body_site, expression_type, false, None);
        }
        Some(result)
    }
}

enum OperationTransfer {
    Value(Type),
    Stop,
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
            let previous_suppression = self.analyzer.reporting.suppress_diagnostics;
            if operation.suppress_diagnostics {
                self.analyzer.reporting.suppress_diagnostics = true;
            }
            let operation_result = (|| -> Result<OperationTransfer, String> {
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
                            cfg::Place::InstanceVariable(name) => {
                                Read::InstanceVariable(name.clone())
                            }
                            cfg::Place::ClassVariable(name) => Read::ClassVariable(name.clone()),
                            cfg::Place::Global(name) => Read::Global(name.clone()),
                            cfg::Place::Constant(path) => Read::Constant(path.clone()),
                        };
                        if operation.defer_inline_assertion {
                            let previous = self.analyzer.defer_inline_assertions;
                            self.analyzer.defer_inline_assertions = true;
                            let type_ = self.analyzer.transfer_cfg_read_at(
                                site,
                                read,
                                &mut next.environment,
                            );
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
                            operation.expression,
                            actual,
                            next.hash_shape(*value),
                            *logical,
                            &mut next.environment,
                        )
                    }
                    cfg::OperationKind::MultiWrite {
                        value,
                        lefts,
                        rest,
                        rights,
                    } => {
                        let actual = next
                            .value(*value)
                            .ok_or_else(|| format!("missing multi-write operand {:?}", value))?;
                        let value_type =
                            if let Some(elements) = self.fixed_array_elements.get(value) {
                                let elements = elements
                                    .iter()
                                    .map(|element| {
                                        next.value(*element).ok_or_else(|| {
                                            format!("missing fixed array element {:?}", element)
                                        })
                                    })
                                    .collect::<Result<Vec<_>, _>>()?;
                                Type::Tuple(elements)
                            } else {
                                actual
                            };
                        super::assignment::transfer_multi_write(
                            self.analyzer,
                            site,
                            value_type,
                            lefts,
                            rest.as_ref(),
                            rights,
                            &mut next.environment,
                        )
                        .ok_or_else(|| {
                            format!("multi-write transfer failed at {:?}", operation.span)
                        })?
                    }
                    cfg::OperationKind::Defined { value } => {
                        next.value(*value)
                            .ok_or_else(|| format!("missing defined? operand {:?}", value))?;
                        self.analyzer.apply_inline_assertion_in_environment_at(
                            site,
                            Type::union([Type::Nil, Type::String]),
                            &next.environment,
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
                            &mut next.hash_shapes,
                            &mut next.environment,
                        )
                        .map_err(|reason| format!("call transfer failed: {reason}"))?;
                        if result.flow.contains(FlowKind::Raise) {
                            let exception = result.abrupt.raise_type.clone();
                            if let Some(edge) = super::exceptions::exception_edge(
                                graph,
                                block,
                                next.clone(),
                                exception.clone(),
                            ) {
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
                            let expression_type = result.normal_type.clone().unwrap_or(Type::Never);
                            self.analyzer.record_at(
                                site,
                                expression_type,
                                self.analyzer.reporting.report,
                                None,
                            );
                            return Ok(OperationTransfer::Stop);
                        }
                        result.normal_type.ok_or_else(|| {
                            format!("call has no normal result at {:?}", operation.span)
                        })?
                    }
                    cfg::OperationKind::BuildArray {
                        elements,
                        preserve_fixed_shape,
                    } => super::construction::transfer_array(
                        self.analyzer,
                        site,
                        elements,
                        &next.values,
                        *preserve_fixed_shape
                            || operation.result.is_some_and(|result| {
                                self.fixed_shape_array_elements.contains_key(&result)
                            }),
                        operation.defer_inline_assertion,
                        &mut next.environment,
                    )
                    .ok_or_else(|| format!("array transfer failed at {:?}", operation.span))?,
                    cfg::OperationKind::BuildHash { elements } => {
                        super::construction::transfer_hash(
                            self.analyzer,
                            site,
                            elements,
                            &next.values,
                            operation.defer_inline_assertion,
                            &mut next.environment,
                        )
                        .ok_or_else(|| format!("hash transfer failed at {:?}", operation.span))?
                    }
                    cfg::OperationKind::Definition { .. } => Type::Nil,
                    cfg::OperationKind::BuildInterpolated { kind } => match kind {
                        crate::hir::InterpolatedKind::String
                        | crate::hir::InterpolatedKind::XString => Type::String,
                        crate::hir::InterpolatedKind::RegularExpression => Type::named("Regexp"),
                        crate::hir::InterpolatedKind::Symbol => Type::Symbol,
                        crate::hir::InterpolatedKind::MatchLastLine => {
                            Type::union([Type::Nil, Type::Integer])
                        }
                    },
                    cfg::OperationKind::BuildRange {
                        left,
                        right,
                        exclude_end: _,
                    } => {
                        let left = left
                            .and_then(|value| next.value(value))
                            .unwrap_or(Type::Nil);
                        let right = right
                            .and_then(|value| next.value(value))
                            .unwrap_or(Type::Nil);
                        let type_ = Type::Named("Range".to_owned(), vec![left, right]);
                        self.analyzer.apply_inline_assertion_in_environment_at(
                            site,
                            type_,
                            &next.environment,
                        )
                    }
                    cfg::OperationKind::Record { value } => {
                        let type_ = value
                            .as_ref()
                            .and_then(|value| next.value(*value))
                            .unwrap_or(Type::Never);
                        self.analyzer.record_at(site, type_.clone(), false, None);
                        type_
                    }
                    cfg::OperationKind::ApplyAssertion { value } => {
                        let type_ = next
                            .value(*value)
                            .ok_or_else(|| format!("missing assertion operand {:?}", value))?;
                        let type_ = self.analyzer.apply_inline_assertion_in_environment_at(
                            site,
                            type_,
                            &next.environment,
                        );
                        let is_send = site.expression.is_some_and(|expression| {
                            self.analyzer
                                .program
                                .hir_program
                                .expression(expression)
                                .is_some_and(|expression| {
                                    matches!(expression.kind, hir::ExprKind::Call(_))
                                })
                        });
                        self.analyzer.record_at(site, type_.clone(), is_send, None);
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
                        let (_, _, type_) = super::patterns::pattern_reachability(
                            self.analyzer,
                            pattern,
                            &source,
                            &next,
                        )
                        .ok_or_else(|| "unsupported pattern reachability".to_owned())?;
                        type_
                    }
                    cfg::OperationKind::MakeClosure { closure } => {
                        let type_ = self
                            .analyzer
                            .cfg_owned_closure_type(*closure, &next.environment)
                            .ok_or_else(|| {
                                format!("closure transfer failed at {:?}", operation.span)
                            })?;
                        if operation.defer_inline_assertion {
                            type_
                        } else {
                            self.analyzer.apply_inline_assertion_in_environment_at(
                                site,
                                type_,
                                &next.environment,
                            )
                        }
                    }
                    _ => return Err(format!("unsupported CFG operation at {:?}", operation.span)),
                };
                let synthetic_safe_navigation_nil =
                    matches!(
                        operation.kind,
                        cfg::OperationKind::Const {
                            value: hir::Literal::Nil
                        }
                    ) && operation.expression.is_some_and(|expression| {
                        self.analyzer
                            .program
                            .hir_program
                            .expression(expression)
                            .is_some_and(|expression| {
                                matches!(expression.kind, hir::ExprKind::Call(_))
                            })
                    });
                if !self.suppress_internal_assignment_record(operation)
                    && !self.suppress_internal_call_record(operation)
                    && !synthetic_safe_navigation_nil
                    && !matches!(
                        operation.kind,
                        cfg::OperationKind::PatternTest { .. }
                            | cfg::OperationKind::Record { .. }
                            | cfg::OperationKind::SetOutcome { .. }
                            | cfg::OperationKind::BindForTarget { .. }
                    )
                {
                    if matches!(operation.kind, cfg::OperationKind::Call { .. }) {
                        self.analyzer.record_at(
                            site,
                            type_.clone(),
                            self.analyzer.reporting.report,
                            None,
                        );
                    } else {
                        self.analyzer.record_at(site, type_.clone(), false, None);
                    }
                }
                Ok(OperationTransfer::Value(type_))
            })();
            if operation.suppress_diagnostics {
                self.analyzer.reporting.suppress_diagnostics = previous_suppression;
            }
            let type_ = match operation_result? {
                OperationTransfer::Value(type_) => type_,
                OperationTransfer::Stop => return Ok(exception_edges),
            };
            if let Some(result) = operation.result {
                next.set_value(result, type_.clone());
                let shape = match &operation.kind {
                    cfg::OperationKind::BuildHash { elements } => {
                        super::super::hash_shape::from_cfg_hash(
                            &self.analyzer.program.hir_program,
                            operation.expression,
                            elements,
                            &next.values,
                            &next.hash_shapes,
                        )
                    }
                    cfg::OperationKind::Read { place } => {
                        super::assignment::hash_shape_key(self.analyzer, place)
                            .and_then(|key| next.environment.hash_shape(&key).cloned())
                    }
                    cfg::OperationKind::Record { value } => {
                        value.and_then(|value| next.hash_shape(value))
                    }
                    cfg::OperationKind::ApplyAssertion { value } => next.hash_shape(*value),
                    _ => None,
                };
                next.set_hash_shape(result, shape);
            }
        }

        let edge = |target, state| cfg::transfer::TransferEdge { target, state };
        match &block.terminator {
            cfg::Terminator::Jump { target, arguments } => {
                if next.pending_exception.is_some()
                    && super::exceptions::is_rescue_entry(graph, block.id)
                {
                    next.handle_exception();
                }
                let target_block = graph
                    .block(*target)
                    .ok_or_else(|| format!("missing jump target {:?}", target))?;
                for (parameter, argument) in target_block.parameters.iter().zip(arguments) {
                    let type_ = next
                        .value(*argument)
                        .ok_or_else(|| format!("missing jump operand {:?}", argument))?;
                    let shape = next.hash_shape(*argument);
                    next.set_value(parameter.value, type_);
                    next.set_hash_shape(parameter.value, shape);
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
                let source_predicate = source_id
                    .and_then(|source_id| pattern_source(graph, source_id))
                    .or_else(|| super::patterns::branch_pattern_source(graph, *condition));
                let source = next
                    .value(source_id.unwrap_or(*condition))
                    .ok_or_else(|| format!("missing branch operand {:?}", condition))?;
                let (truthy_reachable, falsy_reachable) = if let Some(pattern) = pattern {
                    let (truthy, falsy, _) = super::patterns::pattern_reachability(
                        self.analyzer,
                        pattern,
                        &source,
                        &next,
                    )
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
                    super::flow::conditional_reachability(
                        self.analyzer,
                        graph,
                        *truthy,
                        *falsy,
                        &source,
                        &next,
                    )
                };
                let mut edges = Vec::with_capacity(2);
                if truthy_reachable {
                    let mut state = next.clone();
                    if pattern.is_none() {
                        super::flow::narrow_conditional_branch(
                            self.analyzer,
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
                            source_predicate,
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
                        super::flow::narrow_conditional_branch(
                            self.analyzer,
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
                            source_predicate,
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
                if let Some(edge) =
                    super::exceptions::exception_edge(graph, block, next, exception.clone())
                {
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
                        let shape = normal.hash_shape(*argument);
                        normal.set_value(parameter.value, type_);
                        normal.set_hash_shape(parameter.value, shape);
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
                                pending.set_hash_shape(parameter.value, None);
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
                            super::exceptions::exception_edge(graph, block, next, exception.clone())
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
