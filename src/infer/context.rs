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
    pub(super) written_locals: Arc<[hir::LocalId]>,
    pub(super) has_unsupported_operation: bool,
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
        let cfg_body_metadata = cfg_graphs.as_deref().map(|graphs| {
            Arc::<[CfgBodyMetadata]>::from(
                graphs
                    .iter()
                    .map(|graph| build_cfg_body_metadata(graph, rbi_ranges))
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
    let mut written_locals = BTreeSet::new();
    let mut has_unsupported_operation = false;

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
            cfg::OperationKind::Call { arguments, .. } => {
                splatted_values.extend(arguments.iter().filter_map(|argument| match argument {
                    cfg::ArgumentOperand::Splat(value) => Some(*value),
                    _ => None,
                }));
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
        written_locals: Arc::from(written_locals.into_iter().collect::<Vec<_>>()),
        has_unsupported_operation,
    }
}

fn offset_in_ranges(offset: usize, ranges: &[(usize, usize)]) -> bool {
    let index = ranges.partition_point(|(_, end)| *end <= offset);
    ranges
        .get(index)
        .is_some_and(|(start, end)| *start <= offset && offset < *end)
}
