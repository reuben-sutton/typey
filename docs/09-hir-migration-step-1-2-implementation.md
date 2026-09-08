# HIR migration: steps 1 and 2 implementation

This note records the implementation of `docs/09-hir-migration-step-1-2.md`.
The migration was staged as small, reviewable commits. HIR now owns the
semantic shape of calls and assignments; the remaining Prism references are
only child-expression adapters at the current evaluator boundary.

## What landed

* `f7f7d29` added the owned HIR data model: source-mapped spans, stable IDs,
  bodies, closures, calls, arguments, assignments, control-flow expressions,
  declarations, and explicit `Unsupported` expressions.
* `7b9be79` added Prism-to-HIR lowering and lowering tests. The HIR contains no
  `ruby_prism::Node` references.
* `1b7ff91`, `ffc2566`, and `81d2441` routed ordinary call inference through
  HIR call shapes and removed the legacy Prism `CallShape` path.
* `88ff9a0` made nested calls in unsupported parents and parameter defaults
  visible to HIR lowering.
* `a5ed063` added an owned local-name table so HIR local IDs do not need to
  recover names from Prism nodes.
* `18b023d` routed every assignment target and assignment operator through an
  HIR dispatcher: locals, instance/class/global variables, constants,
  attributes, indexes, compound writes, and logical/binary writes. The old
  Prism assignment dispatch tree was removed from the evaluator.
* `52aa847` made call argument bridging HIR-driven, including positional,
  keyword, splat, forwarding, block, index, `yield`, and `super` shapes.
  Nested special calls in unsupported parents are lowered as well.
* `78553e8` preserved generic types through HIR setter writes and added a
  nested generic-constructor regression fixture.
* `355f147` fixed the Prism-vs-HIR representation edge case where a
  brace-less positional hash is exposed by Prism as a keyword-hash node.

Calls retain implicit/explicit/super/yield receivers, safe navigation,
positional and keyword arguments, splats, forwarding, and inline or passed
blocks. Assignments retain their target and operator instead of being erased
during lowering.

## Tests and parity gates

The temporary parity path was run before deleting the legacy call evaluator.
After cleanup, the gates pass with the current fixture set:

* checker: 325 passed;
* conformance: 157 passed;
* HIR tests: 9 passed;
* library tests: 10 passed;
* `cargo fmt -- --check` and `git diff --check`: clean;
* Sorbet on Spoom: no errors;
* Typey on Spoom: the same 3 classified diagnostics as the pre-HIR build.

The new regression coverage includes `tests/fixtures/hir_assignment_dispatch.rb`
and `tests/fixtures/positional_hash_argument.rb`, plus HIR tests for assignment
targets, nested unsupported-parent lowering, nested `yield`, and positional
hash argument shape. The checker and conformance suites were rerun after each
logical migration stage.

The release timing comparison used the clean pre-HIR commit `7433545` and the
current release build on the same Spoom checkout:

* pre-HIR: 3.22s;
* current: 3.13s in the latest release run.

The individual runs are noisy on this small repository, so this is not a
claim of a stable performance improvement. The current path still parses the
source once for Prism-based declaration compatibility and once for owned HIR
lowering; sharing that boundary is a later optimization.

Packwerk also completes without a HIR migration crash. Its remaining findings
are the pre-existing cluster around the malformed minitest shim RBI, missing
test-helper models, and nilability in test code; they were not suppressed by
the migration.

## Remaining Prism boundary

The semantic decisions for calls and assignments now come from HIR. A narrow
adapter still retains Prism child nodes so the existing evaluator can
recursively evaluate receiver, argument, and block expressions while the full
HIR expression evaluator is being built. This is the plan-approved adapter
boundary, not a second source of call or assignment shape.

The lowerer still uses Prism traversal to discover expressions nested inside
parents that do not yet have dedicated HIR variants. Removing that bridge
completely requires an owned expression-to-expression evaluator and CFG, not
another syntax-specific fallback or a broader `T.untyped` escape hatch.
