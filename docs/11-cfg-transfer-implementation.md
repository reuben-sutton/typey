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
* `2d5ae3d` added the inference-side `BlockState`. It owns block value slots,
  environment joins, and abrupt-flow joins; CFG conditional joins now use it
  instead of reaching back to the monolithic evaluator's environment helper.
  Tests cover normal/abrupt merges, two-normal joins, and missing values.
* `29c18e6` moved literal and read transfer to owned HIR. The operation kind,
  literal class, and storage place are selected from HIR; Prism is retained
  only for source recording and inline assertions.
* `4c169c5` moved direct `Set` writes for locals, ivars, class vars, globals,
  and constants to the same owned transfer module. Compound and dynamic
  attribute/index writes remain explicitly bridged.

## Next boundary

The analyzer still uses its recursive evaluator for compound/dynamic operation
semantics, and `BlockState` is not yet driven by the generic worklist for
complete bodies. The next implementation should add `BodyContext` and a
transfer host that adapts `BlockState` to `BlockTransfer`, then move collection
construction, closures, and ordinary calls. The recursive path must remain
available for differential checks until each operation and terminator has an
equivalent transfer.
