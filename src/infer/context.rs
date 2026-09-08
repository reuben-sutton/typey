//! Immutable source, HIR, and CFG inputs shared by inference layers.

use super::{hir, prism, signature};
use crate::cfg;
use std::collections::HashMap;
use std::sync::Arc;

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
        annotations: signature::AnnotationTable,
    ) -> Self {
        let cfg_index = cfg_graphs
            .as_deref()
            .map(|graphs| cfg::CfgIndex::from_graphs(&hir_program, graphs));
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
