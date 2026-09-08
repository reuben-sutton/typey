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
* `4dcb8bc` moved array and hash construction, including keyword-hash and
  collection splats, behind the owned transfer boundary.
* `31c89ea` connected conditional transfer to the generic deterministic
  block worklist. The temporary host still delegates branch-body expression
  semantics to the existing evaluator, but scheduling, reachability, and the
  join now belong to the transfer layer.
* `63f7e81` connected `while`/`until` transfer to the worklist, including
  loop-carried environments and consumed `break`/`next` outcomes.
* `38d2072` optimized the deterministic queue without changing its ordering
  or convergence contract.
* `7e53b4b` connected `for` transfer to the same graph boundary, including
  element binding and loop exits.
* `d60667f` added a complete-body adapter for the first owned HIR subset:
  literals, reads, sequences, and simple storage writes are transferred as
  CFG operations, with method environments and recorded source types updated
  only after a successful preflight. Unsupported bodies continue through the
  recursive evaluator.
* `ceae0ea` extended the complete-body adapter to ordinary calls with implicit
  or explicit receivers and positional arguments. Receiver and argument types
  now come from `BlockState` value IDs, while existing signature dispatch,
  generic-class construction, dependency tracking, and call diagnostics are
  reused at the inference boundary. Calls with keywords, splats, blocks, safe
  navigation, `super`, or `yield` still fall back before partial results are
  recorded.
* `20baa11` moved non-splat array and hash construction onto the same value-ID
  path, including element/key/value joins and hash/array inline assertions.
  Collection splats remain a deliberate fallback: their wrapper source spans
  are not yet represented by the owned CFG operands, and transferring them
  would lose recorded source types.
* `79185dd` admitted binary compound assignments whose target is a direct
  storage place. Their existing owned lowering is a straight-line
  read/call/write sequence, so the body worklist can transfer them without
  adding a second assignment evaluator. `&&=`/`||=` and dynamic compound
  targets remain outside this boundary.
* `fda77a1` extended `Set` transfer to attribute and index targets whose
  receiver and arguments are themselves owned, positional-only expressions.
  The lowered setter calls now use the same call transfer as ordinary sends;
  keyword/splat targets and non-local logical compound forms remain recursive.
* `df09d11` added local `&&=`/`||=` transfer using owned pattern-test and
  branch edges. The host preserves both reachable paths and only records
  source operations that correspond to real expressions. Ivar, class-variable,
  global, and dynamic logical assignments remain recursive until the state
  model carries their assignment-specific non-nil postconditions.

## Next boundary

The analyzer still uses its recursive evaluator for compound/dynamic operation
semantics, rescue/ensure, and branch/body expression adapters. Complete-body
transfer is deliberately narrow: it does not yet interpret keyword/splat/block
calls, safe navigation, `super`, `yield`, closures, or abrupt terminators
inside a body. The next implementation boundaries are the remaining call
shapes, non-local logical compound assignments, and dynamic compound writes,
then complete branch bodies and rescue/ensure edges. Collection splats also need
explicit operand-span metadata before they can cross this boundary. The
recursive path must remain available for differential checks until each
operation and terminator has an equivalent transfer.

The current call adapter is also an explicit bridge: it uses CFG-owned value
IDs for evaluation order and types, but still obtains Prism call nodes for
source recording and the existing dispatch helpers. That bridge should shrink
as call argument metadata and dispatch inputs become owned HIR data.
