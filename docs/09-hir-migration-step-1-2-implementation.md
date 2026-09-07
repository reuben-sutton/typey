# HIR migration: steps 1 and 2 implementation

This note records the implementation of `docs/09-hir-migration-step-1-2.md`.
The migration was deliberately staged so the old and HIR call paths could be
compared before the Prism path was removed.

## What landed

* `f7f7d29` added the owned HIR data model: source-mapped spans, stable IDs,
  bodies, closures, calls, arguments, assignments, control-flow expressions,
  declarations, and explicit `Unsupported` expressions.
* `7b9be79` added Prism-to-HIR lowering and lowering tests. The HIR contains no
  `ruby_prism::Node` references.
* `1b7ff91` routed ordinary call inference through HIR call shapes and added a
  temporary legacy/HIR parity switch.
* `ffc2566` removed the legacy ordinary-call path. Plain attribute and index
  writes were also routed through HIR assignment targets.
* `81d2441` removed the remaining generic Prism `CallShape` abstraction from
  call inference.
* `88ff9a0` made nested calls in unsupported parents and parameter defaults
  visible to HIR lowering.
* `78553e8` preserved the established setter protocol for HIR attribute/index
  writes and added a nested generic-constructor regression fixture. This
  prevents `Element[E]` from becoming `Element[Poset::E]` while retaining the
  HIR assignment as the source-of-truth shape.

Calls retain implicit/explicit/super/yield receivers, safe navigation,
positional and keyword arguments, splats, forwarding, and inline or passed
blocks. Assignments retain their target and operator instead of being erased
during lowering.

## Parity and gates

The temporary parity path was run before deleting the legacy call evaluator.
After cleanup, the gates pass with the current fixture set:

* checker: 323 passed;
* conformance: 156 passed;
* HIR tests: 6 passed;
* library tests: 10 passed;
* `cargo fmt -- --check` and `git diff --check`: clean;
* Sorbet on Spoom: no errors;
* Typey on Spoom: the same 3 classified diagnostics as the pre-HIR build.

The release timing comparison used the clean pre-HIR commit `7433545` and the
current release build on the same Spoom checkout:

* pre-HIR: 3.22s;
* current: 3.43s.

That is approximately 0.21s, or 6.5%, slower on this small repository. The
current path parses the source once for Prism-based declaration/inference
compatibility and once for owned HIR lowering, so this overhead is expected to
be addressed by sharing the parse/lowering boundary in a later step.

## Remaining Prism boundary

The semantic decisions for ordinary calls now come from HIR. A narrow adapter
still retains Prism child nodes so the existing evaluator can recursively
evaluate receiver, argument, and block expressions while the full HIR
expression evaluator is being built. The lowerer also uses a Prism visitor to
find calls nested inside parents that are not yet represented by dedicated HIR
variants.

Assignment evaluation is HIR-directed for plain attribute and index writes;
the setter protocol is constructed from the HIR target and passed through the
HIR call evaluator. Compound/local/ivar/class/global/constant assignment
branches still use Prism accessors to obtain child expressions and are the
next cleanup boundary. They are not application-specific models and should be
moved behind HIR assignment views before CFG migration.

This means steps 1 and 2 are functionally parity-safe, but the Prism child-node
bridge is intentionally still present. Removing it completely requires an
owned expression-to-expression evaluator, not another syntax-specific fallback
or a broader `T.untyped` escape hatch.
