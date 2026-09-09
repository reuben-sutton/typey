//! Generic block scheduling for CFG transfer.
//!
//! This module owns graph traversal and convergence. It deliberately does not
//! know about `Type`, `Environment`, diagnostics, or method summaries; those
//! are supplied by the inference-side transfer implementation.

use super::{BasicBlock, BlockId, Cfg};
use std::cmp::Reverse;
use std::collections::BinaryHeap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferEdge<S> {
    pub target: BlockId,
    pub state: S,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorklistError<E> {
    InvalidBlock(BlockId),
    Transfer(E),
}

/// A host supplies operation and terminator semantics while this module owns
/// deterministic scheduling and state convergence.
pub trait BlockTransfer {
    type State: Clone;
    type Error;

    fn transfer_block(
        &mut self,
        cfg: &Cfg,
        block: &BasicBlock,
        state: &Self::State,
    ) -> Result<Vec<TransferEdge<Self::State>>, Self::Error>;

    /// Return the joined state and whether it is strictly different from the
    /// predecessor state. `None` means the target has not been reached yet.
    fn join_state(
        &mut self,
        current: Option<&Self::State>,
        incoming: Self::State,
    ) -> (Self::State, bool);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorklistResult<S> {
    pub states: Vec<Option<S>>,
    pub visit_order: Vec<BlockId>,
}

/// Interpret a CFG until every reachable block has a stable joined state.
///
/// The pending set is ordered by `BlockId`, making diagnostics and traces
/// reproducible even when a branch contributes both successors.
pub fn run<T>(
    cfg: &Cfg,
    transfer: &mut T,
    initial: T::State,
) -> Result<WorklistResult<T::State>, WorklistError<T::Error>>
where
    T: BlockTransfer,
{
    run_from(cfg, transfer, cfg.entry, initial)
}

/// Interpret a CFG from an explicitly selected block until every reachable
/// block has a stable joined state. This is useful for transfer-side analysis
/// of regions that are structurally present in the graph but are not reached
/// by a currently known outcome, such as rescue handlers.
pub fn run_from<T>(
    cfg: &Cfg,
    transfer: &mut T,
    start: BlockId,
    initial: T::State,
) -> Result<WorklistResult<T::State>, WorklistError<T::Error>>
where
    T: BlockTransfer,
{
    let entry = cfg.block(start).ok_or(WorklistError::InvalidBlock(start))?;
    let _ = entry;
    let mut states = vec![None; cfg.blocks.len()];
    let mut pending = BinaryHeap::new();
    let mut queued = vec![false; cfg.blocks.len()];
    let (entry_state, changed) = transfer.join_state(None, initial);
    states[start.0 as usize] = Some(entry_state);
    if changed {
        pending.push(Reverse(start));
        queued[start.0 as usize] = true;
    }

    let mut visit_order = Vec::new();
    while let Some(Reverse(block_id)) = pending.pop() {
        queued[block_id.0 as usize] = false;
        let Some(state) = states.get(block_id.0 as usize).and_then(Option::as_ref) else {
            return Err(WorklistError::InvalidBlock(block_id));
        };
        let block = cfg
            .block(block_id)
            .ok_or(WorklistError::InvalidBlock(block_id))?;
        visit_order.push(block_id);
        let edges = transfer
            .transfer_block(cfg, block, state)
            .map_err(WorklistError::Transfer)?;
        for edge in edges {
            if cfg.block(edge.target).is_none() {
                return Err(WorklistError::InvalidBlock(edge.target));
            }
            let (joined, changed) =
                transfer.join_state(states[edge.target.0 as usize].as_ref(), edge.state);
            if changed {
                states[edge.target.0 as usize] = Some(joined);
                if !queued[edge.target.0 as usize] {
                    pending.push(Reverse(edge.target));
                    queued[edge.target.0 as usize] = true;
                }
            }
        }
    }

    Ok(WorklistResult {
        states,
        visit_order,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::BodyId;

    struct TestTransfer;

    impl BlockTransfer for TestTransfer {
        type State = u32;
        type Error = ();

        fn transfer_block(
            &mut self,
            _cfg: &Cfg,
            block: &BasicBlock,
            state: &Self::State,
        ) -> Result<Vec<TransferEdge<Self::State>>, Self::Error> {
            Ok(match block.terminator {
                super::super::Terminator::Jump { target, .. } => vec![TransferEdge {
                    target,
                    state: *state,
                }],
                super::super::Terminator::Branch { truthy, falsy, .. } => vec![
                    TransferEdge {
                        target: truthy,
                        state: state.saturating_add(1),
                    },
                    TransferEdge {
                        target: falsy,
                        state: state.saturating_add(2),
                    },
                ],
                super::super::Terminator::EnsureComplete { target, .. } => vec![TransferEdge {
                    target,
                    state: *state,
                }],
                _ => Vec::new(),
            })
        }

        fn join_state(
            &mut self,
            current: Option<&Self::State>,
            incoming: Self::State,
        ) -> (Self::State, bool) {
            match current {
                Some(current) => {
                    let joined = (*current).max(incoming);
                    (joined, joined != *current)
                }
                None => (incoming, true),
            }
        }
    }

    fn graph() -> Cfg {
        Cfg {
            body: BodyId(0),
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    parameters: Vec::new(),
                    operations: Vec::new(),
                    terminator: super::super::Terminator::Branch {
                        condition: super::super::ValueId(0),
                        truthy: BlockId(1),
                        falsy: BlockId(2),
                    },
                    unwind: None,
                },
                BasicBlock {
                    id: BlockId(1),
                    parameters: Vec::new(),
                    operations: Vec::new(),
                    terminator: super::super::Terminator::Jump {
                        target: BlockId(3),
                        arguments: Vec::new(),
                    },
                    unwind: None,
                },
                BasicBlock {
                    id: BlockId(2),
                    parameters: Vec::new(),
                    operations: Vec::new(),
                    terminator: super::super::Terminator::Jump {
                        target: BlockId(3),
                        arguments: Vec::new(),
                    },
                    unwind: None,
                },
                BasicBlock {
                    id: BlockId(3),
                    parameters: Vec::new(),
                    operations: Vec::new(),
                    terminator: super::super::Terminator::Return(None),
                    unwind: None,
                },
            ],
            conditionals: Vec::new(),
            ensure_entries: Vec::new(),
            rescue_regions: Vec::new(),
            unsupported_spans: Vec::new(),
            expression_values: Vec::new(),
        }
    }

    #[test]
    fn visits_branches_in_stable_block_order_and_joins_at_merge() {
        let mut transfer = TestTransfer;
        let result = run(&graph(), &mut transfer, 0).expect("worklist succeeds");
        assert_eq!(
            result.visit_order,
            [BlockId(0), BlockId(1), BlockId(2), BlockId(3)]
        );
        assert_eq!(result.states[3], Some(2));
    }

    #[test]
    fn does_not_visit_unreachable_blocks() {
        let mut graph = graph();
        graph.blocks.push(BasicBlock {
            id: BlockId(4),
            parameters: Vec::new(),
            operations: Vec::new(),
            terminator: super::super::Terminator::Return(None),
            unwind: None,
        });
        let mut transfer = TestTransfer;
        let result = run(&graph, &mut transfer, 0).expect("worklist succeeds");
        assert_eq!(result.states[4], None);
        assert!(!result.visit_order.contains(&BlockId(4)));
    }

    #[test]
    fn rejects_invalid_successor_edges() {
        let mut graph = graph();
        graph.blocks[1].terminator = super::super::Terminator::Jump {
            target: BlockId(99),
            arguments: Vec::new(),
        };
        let mut transfer = TestTransfer;
        assert_eq!(
            run(&graph, &mut transfer, 0),
            Err(WorklistError::InvalidBlock(BlockId(99)))
        );
    }
}
