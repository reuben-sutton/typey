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
* `dfe6009` removed avoidable CFG-index work. Index-only lowering no longer
  builds the full expression span map or clones call names, while full graph
  construction retains expression identity for structural consumers.

The CFG builder has no dependency on `Type`, `Environment`, diagnostics, or
Rails models. Unsupported HIR remains an explicit operation; it is not turned
into a concrete value or silently replaced with `T.untyped`.

## Verification

The current gates pass:

* CFG structural tests: 14 passed;
* HIR lowering tests: 10 passed;
* checker tests: 329 passed;
* conformance tests: 158 passed;
* release Spoom: the same three classified diagnostics as the baseline.

CFG-enabled checker regressions cover ordinary calls, local and instance
writes, attribute setters, loop/rescue fixtures, safe navigation, branches,
compound assignments, and source identity. The default checker remains at
baseline performance because CFG construction is not yet enabled by default.
On the local release benchmark, Spoom took about 2.12s on the legacy path and
1.85s with `--cfg` in the latest run; both paths produced the same three
classified diagnostics. The measurements are close enough that the CFG index
is no longer an unexplained repository-level regression. The remaining
transfer boundary is semantic ownership, not an observed indexing hotspot.

## Remaining migration boundary

The legacy recursive evaluator still owns loop, rescue, ensure, and general
expression transfer. CFG mode now selects conditional branch bodies and joins
from owned CFG regions, while retaining source-node child evaluation as a
temporary bridge. It still uses explicit fallbacks for executable expressions
that are orphaned under unsupported syntax.

The next stages are therefore:

1. transfer loops, `break`, and `next` through CFG edges;
2. transfer rescue, `retry`, and ensure edges;
3. compare diagnostics, inferred types, flow outcomes, send metrics, and
   untyped provenance against the recursive path;
4. remove the opt-in switch and legacy path only after those comparisons are
   complete.

The source-node index and HIR expression IDs are intentionally temporary
bridges for those steps. They should disappear from the final transfer path
once operations can evaluate owned HIR values directly.
