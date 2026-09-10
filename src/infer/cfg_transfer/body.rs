//! Owned CFG transfer for complete HIR bodies.

use super::super::cfg_state::{BlockState, BodyContext};
use super::super::{
    Analyzer, Environment, Eval, Flow, FlowKind, OutcomeTypes, OwnedCallInput, SourceSite,
};
use super::globals::{clear_cfg_global_state, commit_cfg_global_state, seed_cfg_global_state};
use super::patterns::{
    case_match_reachability, narrow_pattern_value, pattern_source, pattern_source_place,
};
use super::preflight;
use crate::cfg;
use crate::hir::{self, Read};
use crate::types::Type;
use std::collections::{HashMap, HashSet};

pub(super) struct BodyTransfer<'analyzer, 'src> {
    pub(super) analyzer: &'analyzer mut Analyzer<'src>,
    pub(super) context: BodyContext,
    pub(super) fixed_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    pub(super) fixed_shape_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    pub(super) normal_type: Type,
    pub(super) abrupt: OutcomeTypes,
    pub(super) terminal_flow: Flow,
    pub(super) final_environment: Option<Environment>,
    pub(super) top_level_terminated: bool,
    /// An isolated transfer of a rescue handler stops at its enclosing
    /// begin-expression's join rather than continuing into the protected
    /// body's following statements.
    probe_exit: Option<cfg::BlockId>,
    probe_protected_entry: Option<cfg::BlockId>,
    probe_normal_type: Type,
    unreachable_probes: Vec<UnreachableProbe>,
    seen_unreachable_probes: HashSet<(cfg::BlockId, cfg::BlockId)>,
    branch_results: HashMap<cfg::BlockId, BranchResult>,
}

#[derive(Clone)]
struct UnreachableProbe {
    start: cfg::BlockId,
    stop: cfg::BlockId,
    state: BlockState,
}

#[derive(Clone)]
struct BranchResult {
    truthy: cfg::BlockId,
    falsy: cfg::BlockId,
    truthy_reachable: bool,
    falsy_reachable: bool,
    state: BlockState,
}

fn contains_class_object(type_: &Type) -> bool {
    match type_ {
        Type::Union(members) => members.iter().any(contains_class_object),
        type_ => Analyzer::class_object_instance_type(type_).is_some(),
    }
}

impl<'analyzer, 'src> BodyTransfer<'analyzer, 'src> {
    fn first_body_expression(&self, expression: hir::ExprId) -> Option<hir::ExprId> {
        match &self
            .analyzer
            .program
            .hir_program
            .expression(expression)?
            .kind
        {
            hir::ExprKind::Sequence(expressions) => expressions
                .first()
                .and_then(|expression| self.first_body_expression(*expression)),
            hir::ExprKind::Begin(begin) => {
                begin.body.and_then(|body| self.first_body_expression(body))
            }
            _ => Some(expression),
        }
    }

    fn should_report_unreachable_branch(&self, expression: hir::ExprId) -> bool {
        let Some(start) = self
            .analyzer
            .program
            .hir_program
            .expression(expression)
            .map(|expression| expression.span.start as usize)
        else {
            return false;
        };
        self.analyzer.program.source[..start]
            .iter()
            .rev()
            .find(|byte| !byte.is_ascii_whitespace())
            .is_none_or(|byte| *byte != b'=')
    }

    fn report_unreachable_branch(
        &mut self,
        graph: &cfg::Cfg,
        truthy: cfg::BlockId,
        falsy: cfg::BlockId,
        state: &BlockState,
    ) {
        let Some(conditional) = graph
            .conditionals
            .iter()
            .find(|conditional| conditional.truthy == truthy && conditional.falsy == falsy)
        else {
            return;
        };
        let Some(hir::ExprKind::Call(call)) = self
            .analyzer
            .program
            .hir_program
            .expression(conditional.condition)
            .map(|expression| &expression.kind)
        else {
            return;
        };
        if !matches!(call.name.as_str(), "is_a?" | "kind_of?" | "instance_of?")
            || !matches!(
                call.arguments.first(),
                Some(hir::Argument::Positional(argument))
                    if matches!(
                        self.analyzer.program.hir_program.expression(*argument).map(|expression| &expression.kind),
                        Some(hir::ExprKind::Read(hir::Read::Constant(_)))
                            | Some(hir::ExprKind::Literal(_))
                    )
            )
        {
            return;
        }
        let hir::Receiver::Explicit(receiver) = call.receiver else {
            return;
        };
        let Some(hir::ExprKind::Read(Read::Local(local))) = self
            .analyzer
            .program
            .hir_program
            .expression(receiver)
            .map(|expression| &expression.kind)
        else {
            return;
        };
        let Some(name) = self
            .analyzer
            .program
            .hir_program
            .local_name(*local)
            .map(|name| name.as_str().to_owned())
        else {
            return;
        };
        let current = state.environment.get(&name);
        let Some(hir::Argument::Positional(argument)) = call.arguments.first() else {
            return;
        };
        let expected = self
            .analyzer
            .cfg_predicate_argument_type(*argument, &state.environment);
        if contains_class_object(&current)
            || matches!(expected, Type::Any | Type::Anything | Type::TypeVar(_))
        {
            return;
        }
        let (truthy_reachable, falsy_reachable) =
            case_match_reachability(self.analyzer, &current, &expected, true);
        if truthy_reachable && falsy_reachable {
            return;
        }
        if !self.should_report_unreachable_branch(conditional.expression) {
            return;
        }
        let body = if !truthy_reachable {
            Some(conditional.then_body)
        } else {
            conditional.else_body
        };
        let Some(body) = body else {
            return;
        };
        let Some(first) = self.first_body_expression(body) else {
            return;
        };
        let Some(expression) = self.analyzer.program.hir_program.expression(first) else {
            return;
        };
        self.analyzer.error_at(
            SourceSite::from_span(expression.span, Some(first)),
            "This code is unreachable",
        );
    }

    fn report_unreachable_body(&mut self, graph: &cfg::Cfg, body: hir::ExprId) {
        let Some(conditional) = graph.conditionals.iter().find(|conditional| {
            conditional.then_body == body || conditional.else_body == Some(body)
        }) else {
            return;
        };
        if !self.should_report_unreachable_branch(conditional.expression) {
            return;
        }
        let Some(first) = self.first_body_expression(body) else {
            return;
        };
        let Some(expression) = self.analyzer.program.hir_program.expression(first) else {
            return;
        };
        self.analyzer.error_at(
            SourceSite::from_span(expression.span, Some(first)),
            "This code is unreachable",
        );
    }

    fn branch_operands<'graph>(
        &self,
        block: &'graph cfg::BasicBlock,
        condition: cfg::ValueId,
    ) -> (Option<cfg::ValueId>, Option<&'graph cfg::Pattern>) {
        block
            .operations
            .iter()
            .find_map(|operation| match operation.result {
                Some(result) if result == condition => {
                    if let cfg::OperationKind::PatternTest { value, pattern } = &operation.kind {
                        Some((Some(*value), Some(pattern)))
                    } else {
                        Some((None, None))
                    }
                }
                _ => None,
            })
            .unwrap_or((None, None))
    }

    fn branch_reachability(
        &self,
        graph: &cfg::Cfg,
        block: &cfg::BasicBlock,
        state: &BlockState,
        condition: cfg::ValueId,
        truthy: cfg::BlockId,
        falsy: cfg::BlockId,
    ) -> Result<(bool, bool), String> {
        let (source_id, pattern) = self.branch_operands(block, condition);
        let source_place = source_id.and_then(|source_id| pattern_source_place(graph, source_id));
        let source = state
            .value(source_id.unwrap_or(condition))
            .ok_or_else(|| format!("missing branch operand {:?}", condition))?;
        if let Some(pattern) = pattern {
            let (truthy_reachable, falsy_reachable, _) =
                super::patterns::pattern_reachability(self.analyzer, pattern, &source, state)
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
                // legacy/Sorbet assignment protocol, including when the
                // current value is already truthy.
                Ok((true, true))
            } else {
                Ok((truthy_reachable, falsy_reachable))
            }
        } else {
            Ok(super::flow::conditional_reachability(
                self.analyzer,
                graph,
                truthy,
                falsy,
                &source,
                state,
            ))
        }
    }

    fn report_stable_unreachable_branches(&mut self, graph: &cfg::Cfg) {
        let mut branches = self
            .branch_results
            .drain()
            .map(|(block, result)| (block, result))
            .collect::<Vec<_>>();
        branches.sort_by_key(|(block, _)| *block);
        for (_, branch) in branches {
            if branch.truthy_reachable != branch.falsy_reachable {
                let body = graph
                    .conditionals
                    .iter()
                    .find(|conditional| {
                        conditional.truthy == branch.truthy && conditional.falsy == branch.falsy
                    })
                    .and_then(|conditional| {
                        if !branch.truthy_reachable {
                            Some(conditional.then_body)
                        } else {
                            conditional.else_body
                        }
                    });
                if let Some(body) = body {
                    self.report_unreachable_body(graph, body);
                }
            }
            self.report_unreachable_branch(graph, branch.truthy, branch.falsy, &branch.state);
        }
    }

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
        let cfg::OperationKind::Call { name, .. } = &operation.kind else {
            return false;
        };
        let Some(expression) = operation
            .expression
            .and_then(|id| self.analyzer.program.hir_program.expression(id))
        else {
            return false;
        };
        if expression.synthetic {
            // HIR introduces a `!` call for `unless` so the ordinary CFG
            // branch machinery can consume a boolean condition. Its span is
            // the predicate's source span, but it is not a source send.
            return true;
        }
        let is_safe_navigation_call = matches!(
            &expression.kind,
            hir::ExprKind::Call(call) if call.safe_navigation
        );
        if operation.defer_inline_assertion
            && is_safe_navigation_call
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
        if self.probe_exit.is_some() {
            return;
        }
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

    fn branch_state(
        &mut self,
        graph: &cfg::Cfg,
        state: &BlockState,
        source_id: Option<cfg::ValueId>,
        pattern: Option<&cfg::Pattern>,
        target: cfg::BlockId,
        truthy: bool,
        source_place: Option<&cfg::Place>,
        source_predicate: Option<super::patterns::PatternSource>,
    ) -> BlockState {
        let mut branch = state.clone();
        if pattern.is_none() {
            super::flow::narrow_conditional_branch(
                self.analyzer,
                graph,
                target,
                truthy,
                &mut branch.environment,
            );
        } else if let Some(source_id) = source_id {
            let pattern = pattern.expect("pattern was present");
            narrow_pattern_value(
                self.analyzer,
                &mut branch,
                source_id,
                pattern,
                truthy,
                source_place,
                source_predicate,
            );
            if branch.pending_exception.is_some() && matches!(pattern, cfg::Pattern::Case { .. }) {
                branch.handle_exception();
            }
        }
        branch
    }

    fn queue_unreachable_probe(
        &mut self,
        start: cfg::BlockId,
        stop: Option<cfg::BlockId>,
        state: BlockState,
    ) {
        let Some(stop) = stop else {
            return;
        };
        if self.seen_unreachable_probes.insert((start, stop)) {
            self.unreachable_probes
                .push(UnreachableProbe { start, stop, state });
        }
    }

    fn transfer_unreachable_probes(&mut self, graph: &cfg::Cfg) -> Result<(), String> {
        let mut index = 0;
        while index < self.unreachable_probes.len() {
            let probe = self.unreachable_probes[index].clone();
            index += 1;

            let normal_type = self.normal_type.clone();
            let abrupt = self.abrupt.clone();
            let terminal_flow = self.terminal_flow;
            let final_environment = self.final_environment.clone();
            let top_level_terminated = self.top_level_terminated;
            let previous_probe_exit = self.probe_exit;
            let previous_probe_protected_entry = self.probe_protected_entry;
            let previous_probe_normal_type = self.probe_normal_type.clone();

            self.probe_exit = Some(probe.stop);
            self.probe_protected_entry = previous_probe_protected_entry;
            self.probe_normal_type = Type::Never;
            self.branch_results.clear();
            let result = cfg::transfer::run_from(graph, self, probe.start, probe.state);

            self.normal_type = normal_type;
            self.abrupt = abrupt;
            self.terminal_flow = terminal_flow;
            self.final_environment = final_environment;
            self.top_level_terminated = top_level_terminated;
            self.probe_exit = previous_probe_exit;
            self.probe_protected_entry = previous_probe_protected_entry;
            self.probe_normal_type = previous_probe_normal_type;

            match result {
                Ok(_) => {
                    self.report_stable_unreachable_branches(graph);
                }
                Err(cfg::transfer::WorklistError::InvalidBlock(block)) => {
                    return Err(format!("unreachable probe reached invalid block {block:?}"));
                }
                Err(cfg::transfer::WorklistError::Transfer(reason)) => {
                    return Err(format!("unreachable probe transfer failed: {reason}"));
                }
            }
        }
        Ok(())
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
        let body = self.program.hir_program.body(body_id)?;
        if let Some(failure) = preflight::body_transfer_failure_ignoring_ranges(
            &self.program.hir_program,
            body_id,
            &self.rbi_ranges,
        ) {
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
                if self.is_rbi_offset(operation.span.start as usize) {
                    return false;
                }
                !matches!(
                    operation.kind,
                    cfg::OperationKind::Const { .. }
                        | cfg::OperationKind::Read { .. }
                        | cfg::OperationKind::ReadSpecial { .. }
                        | cfg::OperationKind::Write { .. }
                        | cfg::OperationKind::MultiWrite { .. }
                        | cfg::OperationKind::MultiWriteElement { .. }
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
            top_level: matches!(body.owner, hir::BodyOwner::TopLevel),
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
        let mut written_locals = HashSet::new();
        for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
            let mut collect_target = |target: &hir::AssignTarget| {
                if let hir::AssignTarget::Local(local) = target {
                    written_locals.insert(*local);
                }
            };
            match &operation.kind {
                cfg::OperationKind::Write {
                    place: cfg::Place::Local(local),
                    ..
                } => {
                    written_locals.insert(*local);
                }
                cfg::OperationKind::MultiWrite {
                    lefts,
                    rest,
                    rights,
                    ..
                } => {
                    lefts.iter().for_each(&mut collect_target);
                    if let Some(rest) = rest {
                        collect_target(rest);
                    }
                    rights.iter().for_each(&mut collect_target);
                }
                cfg::OperationKind::BindForTarget { target, .. } => collect_target(target),
                _ => {}
            }
        }
        for local in written_locals {
            if let Some(name) = self.program.hir_program.local_name(local) {
                if !initial_environment.contains(name.as_str()) {
                    initial_environment.bind(name.as_str().to_owned(), Type::Nil);
                }
            }
        }
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
            top_level_terminated: false,
            probe_exit: None,
            probe_protected_entry: None,
            probe_normal_type: Type::Never,
            unreachable_probes: Vec::new(),
            seen_unreachable_probes: HashSet::new(),
            branch_results: HashMap::new(),
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
        transfer.report_stable_unreachable_branches(&graph);
        if let Err(reason) = transfer.transfer_unreachable_probes(&graph) {
            transfer.analyzer.record_cfg_fallback_detail_at(
                body_site,
                "unreachable branch",
                super::CfgFallbackKind::UnsupportedOperation,
                Some(&reason),
            );
            return None;
        }
        let mut normal_type = transfer.normal_type.clone();
        for region in &graph.rescue_regions {
            let Some(entry_block) = graph.block(region.entry) else {
                continue;
            };
            let Some(exception_parameter) = entry_block.parameters.first() else {
                continue;
            };
            let mut probe_environment = worklist
                .states
                .get(region.protected_entry.0 as usize)
                .and_then(Option::as_ref)
                .map(|state| state.environment.clone())
                .unwrap_or_else(|| fallback_environment.clone());
            seed_cfg_global_state(transfer.analyzer, &graph, &mut probe_environment);
            let mut probe = BlockState::with_values(
                probe_environment,
                Vec::new(),
                Flow::abrupt(FlowKind::Raise),
            );
            probe.route_exception(Type::Any);
            probe.set_value(exception_parameter.value, Type::Any);
            let main_abrupt = transfer.abrupt.clone();
            let main_terminal_flow = transfer.terminal_flow;
            let main_final_environment = transfer.final_environment.clone();
            let main_top_level_terminated = transfer.top_level_terminated;
            transfer.probe_exit = Some(region.exit);
            transfer.probe_protected_entry = Some(region.protected_entry);
            transfer.probe_normal_type = Type::Never;
            transfer.branch_results.clear();
            let probe_result = cfg::transfer::run_from(&graph, &mut transfer, region.entry, probe);
            transfer.probe_exit = None;
            transfer.probe_protected_entry = None;
            transfer.abrupt = main_abrupt;
            transfer.terminal_flow = main_terminal_flow;
            transfer.final_environment = main_final_environment;
            transfer.top_level_terminated = main_top_level_terminated;
            if probe_result.is_ok() {
                transfer.report_stable_unreachable_branches(&graph);
            }
            if let Err(error) = probe_result {
                match error {
                    cfg::transfer::WorklistError::InvalidBlock(_) => {
                        transfer.analyzer.record_cfg_fallback_at(
                            body_site,
                            "rescue edge",
                            super::CfgFallbackKind::UnsupportedEdge,
                        );
                    }
                    cfg::transfer::WorklistError::Transfer(reason) => {
                        transfer.analyzer.record_cfg_fallback_detail_at(
                            body_site,
                            "rescue handler",
                            super::CfgFallbackKind::UnsupportedOperation,
                            Some(&reason),
                        );
                    }
                }
                return None;
            }
            transfer.normal_type = normal_type.clone();
            let handler_reached = worklist
                .states
                .get(region.entry.0 as usize)
                .is_some_and(Option::is_some);
            if region.may_raise && !handler_reached && !transfer.probe_normal_type.is_never() {
                normal_type = if normal_type.is_never() {
                    transfer.probe_normal_type.clone()
                } else {
                    normal_type.join(&transfer.probe_normal_type)
                };
            }
        }
        transfer.normal_type = normal_type;
        let normal_type = if transfer.top_level_terminated {
            Type::Never
        } else {
            transfer.normal_type.clone()
        };
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
        if self.probe_exit == Some(block.id) || self.probe_protected_entry == Some(block.id) {
            if let Some(parameter) = block.parameters.first() {
                if let Some(type_) = state.value(parameter.value) {
                    self.probe_normal_type = if self.probe_normal_type.is_never() {
                        type_
                    } else {
                        self.probe_normal_type.join(&type_)
                    };
                }
            }
            return Ok(Vec::new());
        }
        let _strictness = self.context.strictness;
        let mut next = state.clone();
        let mut exception_edges = Vec::new();
        for operation in &block.operations {
            // Vendored RBI files are declaration input, not executable Ruby.
            // Their combined top-level graph can still contain parser-shaped
            // operations such as `undef` or placeholder assignments; ignore
            // those operations just as declaration bodies are ignored.
            if self.analyzer.is_rbi_offset(operation.span.start as usize) {
                if let Some(result) = operation.result {
                    next.set_value(result, Type::Nil);
                }
                continue;
            }
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
                            operation.expression,
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
                    cfg::OperationKind::MultiWriteElement { value, part } => {
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
                        let known_length = match &value_type {
                            Type::Tuple(elements) => Some(elements.len()),
                            _ => None,
                        };
                        match part {
                            cfg::MultiWritePart::Left(index) => self
                                .analyzer
                                .multi_assignment_element_type(&value_type, *index, known_length),
                            cfg::MultiWritePart::Rest => {
                                let element_type = self.analyzer.array_element_type(&value_type);
                                Type::union([Type::Nil, Type::Array(Box::new(element_type))])
                            }
                            cfg::MultiWritePart::Right {
                                index,
                                left_count,
                                right_count,
                            } => {
                                let right_start = known_length
                                    .map(|length| {
                                        (*left_count).max(length.saturating_sub(*right_count))
                                    })
                                    .unwrap_or(0);
                                self.analyzer.multi_assignment_element_type(
                                    &value_type,
                                    right_start + *index,
                                    known_length,
                                )
                            }
                        }
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
                        let mut result = super::calls::transfer_call(
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
                        if self.context.method.is_none()
                            && block.unwind.is_none()
                            && result.flow.contains(FlowKind::Raise)
                        {
                            // At the top level, a terminating method call is
                            // represented as `T.noreturn` by the recursive
                            // evaluator. There is no rescue edge here, so it
                            // must not widen the enclosing program value to
                            // the fallback exception class.
                            result.abrupt.raise_type = Type::Never;
                        }
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
                            if self.context.method.is_some() || block.unwind.is_some() {
                                return Ok(OperationTransfer::Stop);
                            }
                            if self.context.top_level && self.probe_exit.is_none() {
                                self.top_level_terminated = true;
                            }
                            // Top-level Ruby keeps checking later statements
                            // after a raising expression for reveals and
                            // diagnostics. Preserve that behavior by carrying
                            // the non-normal value through the owned graph;
                            // method and closure bodies still terminate here.
                            result.normal_type.unwrap_or(Type::Never)
                        } else {
                            result.normal_type.ok_or_else(|| {
                                format!("call has no normal result at {:?}", operation.span)
                            })?
                        }
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
                    cfg::OperationKind::Definition { declaration, value } => {
                        let context_type = value.and_then(|value| next.value(value));
                        if let Some(value) = value {
                            next.value(*value).ok_or_else(|| {
                                format!("missing declaration operand {:?}", value)
                            })?;
                        }
                        self.analyzer
                            .eval_owned_definition(
                                *declaration,
                                context_type,
                                &mut next.environment,
                            )
                            .map_err(|reason| format!("definition transfer failed: {reason}"))?
                    }
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
                let synthetic_conditional_nil = self.probe_exit.is_some()
                    && matches!(
                        operation.kind,
                        cfg::OperationKind::Const {
                            value: hir::Literal::Nil
                        }
                    )
                    && operation.expression.is_some_and(|expression| {
                        graph
                            .conditionals
                            .iter()
                            .any(|conditional| conditional.expression == expression)
                    });
                if !self.suppress_internal_assignment_record(operation)
                    && !self.suppress_internal_call_record(operation)
                    && !synthetic_safe_navigation_nil
                    && !synthetic_conditional_nil
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
                let (source_id, pattern) = self.branch_operands(block, *condition);
                let source_place =
                    source_id.and_then(|source_id| pattern_source_place(graph, source_id));
                let source_predicate = source_id
                    .and_then(|source_id| pattern_source(graph, source_id))
                    .or_else(|| super::patterns::branch_pattern_source(graph, *condition));
                let (truthy_reachable, falsy_reachable) =
                    self.branch_reachability(graph, block, &next, *condition, *truthy, *falsy)?;
                self.branch_results.insert(
                    block.id,
                    BranchResult {
                        truthy: *truthy,
                        falsy: *falsy,
                        truthy_reachable,
                        falsy_reachable,
                        state: next.clone(),
                    },
                );
                let conditional_join = graph
                    .conditionals
                    .iter()
                    .find(|conditional| {
                        conditional.truthy == *truthy && conditional.falsy == *falsy
                    })
                    .map(|conditional| conditional.join);
                let mut edges = Vec::with_capacity(2);
                let truthy_state = self.branch_state(
                    graph,
                    &next,
                    source_id,
                    pattern.as_deref(),
                    *truthy,
                    true,
                    source_place.as_ref(),
                    source_predicate,
                );
                if truthy_reachable {
                    let state = truthy_state;
                    edges.push(edge(*truthy, state));
                } else {
                    self.queue_unreachable_probe(*truthy, conditional_join, truthy_state);
                }
                let falsy_state = self.branch_state(
                    graph,
                    &next,
                    source_id,
                    pattern.as_deref(),
                    *falsy,
                    false,
                    source_place.as_ref(),
                    source_predicate,
                );
                if falsy_reachable {
                    let state = falsy_state;
                    edges.push(edge(*falsy, state));
                } else {
                    self.queue_unreachable_probe(*falsy, conditional_join, falsy_state);
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
