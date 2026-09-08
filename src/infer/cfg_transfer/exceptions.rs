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
    if let Some(parameter) = target_block.parameters.first() {
        state.set_value(parameter.value, exception.clone());
    }
    state.route_exception(exception);
    Some(cfg::transfer::TransferEdge { target, state })
}

pub(super) fn is_rescue_entry(graph: &cfg::Cfg, block: cfg::BlockId) -> bool {
    graph
        .blocks
        .iter()
        .any(|candidate| candidate.unwind == Some(block))
}
