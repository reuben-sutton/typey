//! Immutable source, HIR, and CFG inputs shared by inference layers.

use super::{hir, prism, signature};
use crate::cfg;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

/// Immutable facts derived from one body-local CFG.
///
/// These facts are independent of the inferred environment, but body
/// transfer may revisit the same graph many times during seeding and
/// fixpoint inference. Keeping the maps behind `Arc` avoids rebuilding and
/// cloning them on every visit.
pub(super) struct CfgBodyMetadata {
    pub(super) fixed_array_elements: Arc<HashMap<cfg::ValueId, Vec<cfg::ValueId>>>,
    pub(super) fixed_shape_array_elements: Arc<HashMap<cfg::ValueId, Vec<cfg::ValueId>>>,
    pub(super) inline_closures: Arc<[hir::ClosureId]>,
    pub(super) straight_line_path: Option<Arc<[cfg::BlockId]>>,
    pub(super) written_locals: Arc<[hir::LocalId]>,
    pub(super) has_unsupported_operation: bool,
    pub(super) has_super_or_yield: bool,
    pub(super) has_known_cfg_failure: bool,
}

/// The immutable program view used by recursive evaluation and CFG transfer.
///
/// Keeping source indexing and owned-program lookup together gives the
/// evaluator layers one dependency boundary. Mutable declarations, fixpoint
/// summaries, and reporting products remain on `Analyzer` because they change
/// during analysis.
pub(super) struct ProgramContext<'src> {
    pub(super) source: &'src [u8],
    pub(super) hir_program: hir::Program,
    pub(super) cfg_index: Option<cfg::CfgIndex>,
    pub(super) cfg_graphs: Option<Arc<[cfg::Cfg]>>,
    pub(super) cfg_body_metadata: Option<Arc<[CfgBodyMetadata]>>,
    pub(super) hir_call_ids: HashMap<(usize, usize), hir::ExprId>,
    pub(super) hir_assignment_ids: HashMap<(usize, usize), hir::ExprId>,
    pub(super) hir_value_ids: HashMap<(usize, usize), hir::ExprId>,
    pub(super) hir_body_ids: HashMap<(usize, usize), hir::BodyId>,
    pub(super) line_map: prism::LineMap,
    pub(super) has_inline_assertions: bool,
    pub(super) annotations: signature::AnnotationTable,
}

impl<'src> ProgramContext<'src> {
    pub(super) fn new(
        source: &'src [u8],
        hir_program: hir::Program,
        cfg_graphs: Option<Arc<[cfg::Cfg]>>,
        rbi_ranges: &[(usize, usize)],
        annotations: signature::AnnotationTable,
    ) -> Self {
        let cfg_index = cfg_graphs
            .as_deref()
            .map(|graphs| cfg::CfgIndex::from_graphs(&hir_program, graphs));
        let known_cfg_failures = cfg_graphs
            .as_deref()
            .map(|graphs| build_known_cfg_failures(&hir_program, graphs));
        let cfg_body_metadata = cfg_graphs.as_deref().map(|graphs| {
            Arc::<[CfgBodyMetadata]>::from(
                graphs
                    .iter()
                    .enumerate()
                    .map(|(index, graph)| {
                        let mut metadata = build_cfg_body_metadata(graph, rbi_ranges);
                        metadata.has_known_cfg_failure = known_cfg_failures
                            .as_ref()
                            .and_then(|failures| failures.get(index))
                            .copied()
                            .unwrap_or(false);
                        metadata
                    })
                    .collect::<Vec<_>>(),
            )
        });
        let mut hir_call_ids = HashMap::new();
        let mut hir_assignment_ids = HashMap::new();
        let mut hir_value_ids = HashMap::new();
        let hir_body_ids = hir_program
            .bodies
            .iter()
            .enumerate()
            .map(|(index, body)| {
                (
                    (body.span.start as usize, body.span.end as usize),
                    hir::BodyId(index as u32),
                )
            })
            .collect::<HashMap<_, _>>();
        for (index, expression) in hir_program.expressions.iter().enumerate() {
            let span = (expression.span.start as usize, expression.span.end as usize);
            match &expression.kind {
                hir::ExprKind::Call(_) => {
                    hir_call_ids
                        .entry(span)
                        .or_insert(hir::ExprId(index as u32));
                }
                hir::ExprKind::Assign { .. } => {
                    hir_assignment_ids
                        .entry(span)
                        .or_insert(hir::ExprId(index as u32));
                }
                hir::ExprKind::Nil | hir::ExprKind::Literal(_) | hir::ExprKind::Read(_) => {
                    hir_value_ids
                        .entry(span)
                        .or_insert(hir::ExprId(index as u32));
                }
                _ => {}
            }
        }

        Self {
            source,
            hir_program,
            cfg_index,
            cfg_graphs,
            cfg_body_metadata,
            hir_call_ids,
            hir_assignment_ids,
            hir_value_ids,
            hir_body_ids,
            line_map: prism::LineMap::new(source),
            has_inline_assertions: !annotations.assertions.is_empty(),
            annotations,
        }
    }
}

fn build_cfg_body_metadata(graph: &cfg::Cfg, rbi_ranges: &[(usize, usize)]) -> CfgBodyMetadata {
    let mut fixed_array_elements = HashMap::new();
    let mut splatted_values = HashSet::new();
    let mut inline_closures = BTreeSet::new();
    let mut written_locals = BTreeSet::new();
    let mut has_unsupported_operation = false;
    let mut has_super_or_yield = false;

    for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
        if !offset_in_ranges(operation.span.start as usize, rbi_ranges)
            && !matches!(
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
        {
            has_unsupported_operation = true;
        }

        match &operation.kind {
            cfg::OperationKind::BuildArray { elements, .. } => {
                if let Some(result) = operation.result {
                    if let Some(elements) = elements
                        .iter()
                        .map(|element| match element {
                            cfg::ArrayOperand::Value(value) => Some(*value),
                            cfg::ArrayOperand::Splat { .. } => None,
                        })
                        .collect::<Option<Vec<_>>>()
                    {
                        fixed_array_elements.insert(result, elements);
                    }
                }
            }
            cfg::OperationKind::Call {
                arguments,
                receiver,
                block,
                ..
            } => {
                splatted_values.extend(arguments.iter().filter_map(|argument| match argument {
                    cfg::ArgumentOperand::Splat(value) => Some(*value),
                    _ => None,
                }));
                has_super_or_yield |= matches!(
                    receiver,
                    cfg::ReceiverOperand::Super | cfg::ReceiverOperand::Yield
                );
                if let Some(cfg::BlockOperand::Inline(closure)) = block {
                    inline_closures.insert(*closure);
                }
            }
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
                for target in lefts.iter().chain(rest.iter()).chain(rights.iter()) {
                    if let hir::AssignTarget::Local(local) = target {
                        written_locals.insert(*local);
                    }
                }
            }
            cfg::OperationKind::BindForTarget { target, .. } => {
                if let hir::AssignTarget::Local(local) = target {
                    written_locals.insert(*local);
                }
            }
            _ => {}
        }
    }

    let fixed_shape_array_elements = fixed_array_elements
        .iter()
        .filter(|(value, _)| splatted_values.contains(value))
        .map(|(value, elements)| (*value, elements.clone()))
        .collect();

    CfgBodyMetadata {
        fixed_array_elements: Arc::new(fixed_array_elements),
        fixed_shape_array_elements: Arc::new(fixed_shape_array_elements),
        inline_closures: Arc::from(inline_closures.into_iter().collect::<Vec<_>>()),
        straight_line_path: cfg::transfer::straight_line_path(graph, graph.entry).map(Arc::from),
        written_locals: Arc::from(written_locals.into_iter().collect::<Vec<_>>()),
        has_unsupported_operation,
        has_super_or_yield,
        has_known_cfg_failure: false,
    }
}

fn build_known_cfg_failures(program: &hir::Program, graphs: &[cfg::Cfg]) -> Vec<bool> {
    fn visit(
        program: &hir::Program,
        graphs: &[cfg::Cfg],
        body_id: hir::BodyId,
        memo: &mut [Option<bool>],
        visiting: &mut HashSet<hir::BodyId>,
    ) -> bool {
        if let Some(failure) = memo.get(body_id.0 as usize).and_then(|failure| *failure) {
            return failure;
        }
        if !visiting.insert(body_id) {
            return false;
        }
        let failure = match (program.body(body_id), graphs.get(body_id.0 as usize)) {
            (Some(body), Some(graph)) => {
                let body_has_context = matches!(&body.owner, hir::BodyOwner::Method { .. });
                graph
                    .blocks
                    .iter()
                    .flat_map(|block| &block.operations)
                    .any(|operation| match &operation.kind {
                        cfg::OperationKind::Call { receiver, .. }
                            if matches!(
                                receiver,
                                cfg::ReceiverOperand::Super | cfg::ReceiverOperand::Yield
                            ) =>
                        {
                            !body_has_context
                        }
                        cfg::OperationKind::Definition { declaration, .. } => program
                            .declaration(*declaration)
                            .is_some_and(|declaration| match &declaration.kind {
                                hir::DeclarationKind::Method { body, .. }
                                | hir::DeclarationKind::Class {
                                    body: Some(body), ..
                                }
                                | hir::DeclarationKind::Module {
                                    body: Some(body), ..
                                }
                                | hir::DeclarationKind::SingletonClass {
                                    body: Some(body), ..
                                } => visit(program, graphs, *body, memo, visiting),
                                hir::DeclarationKind::Class { body: None, .. }
                                | hir::DeclarationKind::Module { body: None, .. }
                                | hir::DeclarationKind::SingletonClass { body: None, .. } => false,
                            }),
                        cfg::OperationKind::MakeClosure { closure } => {
                            program.closure(*closure).is_some_and(|closure| {
                                visit(program, graphs, closure.body, memo, visiting)
                            })
                        }
                        _ => false,
                    })
            }
            _ => false,
        };
        visiting.remove(&body_id);
        if let Some(slot) = memo.get_mut(body_id.0 as usize) {
            *slot = Some(failure);
        }
        failure
    }

    let mut memo = vec![None; graphs.len()];
    let mut visiting = HashSet::new();
    for index in 0..graphs.len() {
        let _ = visit(
            program,
            graphs,
            hir::BodyId(index as u32),
            &mut memo,
            &mut visiting,
        );
    }
    memo.into_iter()
        .map(|failure| failure.unwrap_or(false))
        .collect()
}

fn offset_in_ranges(offset: usize, ranges: &[(usize, usize)]) -> bool {
    let index = ranges.partition_point(|(_, end)| *end <= offset);
    ranges
        .get(index)
        .is_some_and(|(start, end)| *start <= offset && offset < *end)
}
