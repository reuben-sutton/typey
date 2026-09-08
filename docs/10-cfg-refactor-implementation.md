# CFG refactor implementation status

This note records the implementation of the first CFG migration stages in
`docs/10-cfg-refactor.md`. The migration is deliberately opt-in while the
recursive evaluator remains the compatibility baseline.

## Completed stages

* `57562b7` added the owned CFG model and pure HIR-to-CFG lowering. CFGs have
  body-local block and value IDs, block parameters, source spans, storage
  places, calls with preserved argument shapes, collection operations,
  pattern tests, jumps, branches, returns, raises, and unwind successors.
* `bf03713` compiled every lowered HIR body once when CFG mode is enabled and
  added the first checker differential boundary.
* `4db57ba` routed supported ordinary calls and assignment sites through CFG
  transfer entry points. The transfer still delegates child-expression
  evaluation to the existing machinery, so receiver and argument evaluation
  retain their established behavior.
* `1dd8b09` made executable expressions nested under unsupported Prism parents
  owned HIR children. They can now appear in the enclosing CFG instead of
  becoming orphaned span lookups.
* `adb087c` attached the originating HIR expression ID to each CFG operation.
* `1c2c3ef` added the opt-in Prism child-node index used by the temporary
  transfer bridge.
* `ceb682f` exposed the migration path as `typey --cfg`.
* The current work records owned conditional regions and transfers `if`
  branches and joins through those regions while retaining the existing flow
  lattice and source-node child evaluation.
* `29c18e6` and `4c169c5` moved literal/read operations and direct storage
  writes into the inference-side CFG transfer module. Compound and dynamic
  writes remain explicit compatibility bridges.
* `4dcb8bc` moved collection construction into owned transfer, and `31c89ea`
  made the CFG conditional scheduler use the generic transfer worklist.
* `63f7e81` moved `while`/`until` loop headers, back-edges, exits,
  `break`, and `next` through the same worklist. `for`, rescue, and ensure
  remain separate migration boundaries.
* `38d2072` replaced the transfer queue's ordered tree with a deterministic
  min-heap and in-queue bitset; the block visit order is unchanged.
* `dfe6009` removed avoidable CFG-index work. Index-only lowering no longer
  builds the full expression span map or clones call names, while full graph
  construction retains expression identity for structural consumers.
* `7e53b4b` moved `for` collection exits, element binding, loop-carried
  environments, and `break`/`next` handling through the same worklist.
* `d60667f` added the first complete-body transfer host. Straight-line method
  bodies containing literals, reads, sequences, and simple storage writes now
  run entirely through owned HIR CFG operations and the generic transfer
  scheduler. The host preflights unsupported operations and falls back before
  recording any partial result.
* `ceae0ea` extended that host to ordinary positional calls. Complete bodies
  now transfer receiver and argument values through CFG state before invoking
  the existing inference-side signature and dispatch machinery; unsupported
  call shapes still use the recursive compatibility path.
* `20baa11` extended complete-body transfer to non-splat array and hash
  construction. Splat wrappers remain an explicit fallback until their source
  spans are represented in CFG operands.
* `79185dd` admitted binary compound assignments on direct storage places via
  their existing CFG read/call/write sequence; logical and dynamic compound
  forms remain explicit fallback boundaries.
* `fda77a1` extended `Set` transfer to owned attribute and index targets when
  their receiver and arguments are positional-only expressions.
* `df09d11` added local logical-assignment branches to the complete-body
  worklist; non-local logical assignments remain explicit fallbacks until
  their postcondition facts are represented in transfer state.
* `7b61018` extended complete-body calls to fixed keyword arguments while
  retaining keyword splats, forwarding, and blocks as explicit fallbacks.
* `1b91c1a` caches the index-compatible body graphs for the lifetime of one
  analyzer. CFG lowering is no longer repeated for each seed, fixpoint, or
  final method visit; the immutable graphs are shared by the CFG index and
  the transfer host.

The CFG builder has no dependency on `Type`, `Environment`, diagnostics, or
Rails models. Unsupported HIR remains an explicit operation; it is not turned
into a concrete value or silently replaced with `T.untyped`.

## Verification

The current gates pass:

* CFG structural tests: 15 passed;
* HIR lowering tests: 10 passed;
* checker tests: 331 passed;
* conformance tests: 160 passed;
* release Spoom: the same three classified diagnostics as the baseline.

CFG-enabled checker regressions cover ordinary calls, local and instance
writes, attribute setters, loop/rescue fixtures, safe navigation, branches,
compound assignments, source identity, and a complete straight-line method
body. The default checker remains at baseline performance because CFG
construction is not yet enabled by default. In three sequential local release
runs, Spoom took 1.71–1.76s with `--cfg` and 1.67–1.75s on the legacy path;
both paths produced the same three classified diagnostics. The CFG body host
transferred 603 methods and 59,187 calls, with 157 legacy body fallbacks. An
initial slower result was traced to rebuilding the program-wide HIR expression
index once per method; the body host now uses the index-free builder, and the
remaining run-to-run difference is negligible.

## Remaining migration boundary

The legacy recursive evaluator still owns rescue, ensure, and general
expression transfer. CFG mode now selects conditional and loop regions from
owned CFGs, and complete straight-line method bodies use the generic worklist.
Conditional and loop bodies still retain source-node child evaluation as a
temporary bridge. It still uses explicit fallbacks for executable expressions
that are orphaned under unsupported syntax.

The next stages are therefore:

1. transfer the remaining call shapes and compound/dynamic writes;
2. transfer rescue, `retry`, ensure edges, and complete branch bodies;
3. compare diagnostics, inferred types, flow outcomes, send metrics, and
   untyped provenance against the recursive path;
4. remove the opt-in switch and legacy path only after those comparisons are
   complete.

The source-node index and HIR expression IDs are intentionally temporary
bridges for those steps. They should disappear from the final transfer path
once operations can evaluate owned HIR values directly.
