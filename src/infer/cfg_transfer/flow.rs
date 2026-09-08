//! Owned CFG branch reachability and predicate refinement.

use super::super::cfg_state::BlockState;
use super::super::{Analyzer, Environment};
use super::patterns::truthiness_reachability;
use crate::cfg;
use crate::hir::{self, Read};
use crate::types::Type;

pub(super) fn narrow_conditional_branch(
    analyzer: &mut Analyzer<'_>,
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
    analyzer.narrow_cfg_predicate(conditional.condition, environment, truthy);
}

pub(super) fn conditional_reachability(
    analyzer: &Analyzer<'_>,
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
        .and_then(|condition| analyzer.program.hir_program.expression(condition))
        .map(|expression| &expression.kind)
    {
        let Some(name) = analyzer.program.hir_program.local_name(*local) else {
            return truthiness_reachability(source);
        };
        if state.environment.is_inferred(name.as_str()) {
            return (true, true);
        }
    }
    truthiness_reachability(source)
}
