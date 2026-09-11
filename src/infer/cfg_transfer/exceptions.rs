//! Owned CFG exception-edge routing.

use super::super::cfg_state::BlockState;
use crate::cfg;
use crate::types::Type;

pub(super) fn exception_edge(
    graph: &cfg::Cfg,
    block: &cfg::BasicBlock,
    mut state: BlockState,
    exception: Type,
) -> Option<cfg::transfer::TransferEdge<BlockState>> {
    let target = block.unwind?;
    let target_block = graph.block(target)?;
    if !graph.ensure_entries.contains(&target) {
        if let Some(parameter) = target_block.parameters.first() {
            state.set_value(parameter.value, exception.clone());
        }
    } else if let Some(parameter) = target_block.parameters.first() {
        // The first parameter of an ensure entry is the protected expression
        // value, not an exception slot.  Keep a bottom placeholder so a
        // normal value survives the join while the exceptional path remains
        // unable to use it for normal completion.
        state.set_value(parameter.value, Type::Never);
    }
    state.route_exception(exception);
    // An ensure body executes normally even when it is cleaning up an
    // exceptional path.  Keep the pending exception so EnsureComplete can
    // rethrow it, but mark the transfer as normal as well.  This makes the
    // ensure entry join its normal and exceptional environments instead of
    // discarding locals that were not assigned before the exception.
    if graph.ensure_entries.contains(&target) {
        state.flow = state.flow.union(crate::infer::Flow::normal());
    }
    Some(cfg::transfer::TransferEdge { target, state })
}

pub(super) fn is_rescue_entry(graph: &cfg::Cfg, block: cfg::BlockId) -> bool {
    graph
        .blocks
        .iter()
        .any(|candidate| candidate.unwind == Some(block))
}
