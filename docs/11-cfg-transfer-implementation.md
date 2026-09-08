# CFG transfer implementation status

The transfer phase now has its first owned behavior boundary. The generic
block worklist in `src/cfg/transfer.rs` owns deterministic scheduling,
reachable-state slots, successor validation, and convergence. Inference-side
code will provide operation semantics and the state join; the CFG layer does
not depend on `Type`, `Environment`, diagnostics, or method summaries.

## Completed

* The worklist uses ordered `BlockId`s, so branch traversal is reproducible.
* Unreached blocks remain `None` and are never represented as `T.untyped`.
* A successor is requeued only when the host reports a changed joined state.
* Invalid entry and successor IDs are rejected explicitly.
* Unit coverage exercises branch joins, unreachable blocks, and invalid edges.

## Next boundary

The analyzer still uses its recursive evaluator for operation semantics. The
next implementation should introduce a transfer-owned `BlockState` and adapt
the existing `Environment`/`Eval` lattice to `BlockTransfer`, first for
constants, reads, writes, closures, and ordinary calls. The recursive path
must remain available for differential checks until each operation and
terminator has an equivalent transfer.
