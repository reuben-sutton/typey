# CFG transfer completion and legacy-bridge retirement

This is the next implementation step after the HIR and CFG work described in
`docs/09-hir-migration-step-1-2.md`, `docs/10-cfg-refactor.md`, and
`docs/11-cfg-transfer-and-abstract-interpreter.md`.

The repository has already crossed the architectural boundary that the older
transfer spec described. Typey now has:

* owned HIR and pure HIR-to-CFG lowering;
* cached, body-local CFGs with block parameters, value IDs, calls, writes,
  collection operations, pattern tests, branches, loops, and unwind metadata;
* a generic deterministic block worklist in `cfg::transfer`;
* an inference-side `BlockState` and production `BodyTransfer`;
* CFG transfer for literals, reads, direct writes, ordinary calls, arrays,
  hashes, positional splats, ordinary conditionals, and loop regions; and
* an opt-in differential path which falls back to the recursive evaluator
  before publishing a partial result.

The current local gates are 15 CFG tests and 331 checker tests passing. The
implementation note records parity with the existing Spoom baseline. The CFG
path is still opt-in because the transfer host has two semantic bridges: it
looks up Prism nodes by source span and it reconstructs call argument shapes
from Prism children. Conditional and loop regions also still evaluate some
child bodies through the recursive evaluator. A body containing an unsupported
operation, an unmapped source operation, or an unwind edge falls back as a
whole.

The next step is therefore not another scheduler abstraction. It is to make
CFG transfer an owned-HIR abstract interpreter, complete the remaining control
flow, and then measure whether the legacy path is still needed.

## Goals

1. Evaluate every operation in a transferred body from CFG operands and owned
   HIR only.
2. Preserve the existing inference semantics: concrete types whenever proven,
   gradual types only when evidence is absent, path-sensitive environments,
   diagnostics, send recording, method dependencies, and untyped provenance.
3. Transfer the remaining Ruby control-flow and call shapes without silently
   converting them to `T.untyped`.
4. Keep fallback explicit and transactional while migration is in progress.
5. Establish differential evidence strong enough to make CFG the default and
   remove the old recursive body path for migrated syntax.

## Non-goals

This step does not redesign the type lattice, introduce constraints/evidence
objects, or add SCC scheduling. Those may be useful after transfer is direct
and stable. It also does not rewrite application code or project RBIs to make
the CFG path quiet.

## Current boundary

The current implementation has a useful but temporary shape:

```text
owned HIR -> owned CFG -> BlockTransfer
                         |-> source-span Prism lookup
                         |-> existing recursive call/child evaluator
                         |-> whole-body legacy fallback
```

The target shape is:

```text
owned HIR -> owned CFG -> BlockTransfer -> abstract state/result
                                      |-> source spans only for recording
                                      |-> explicit unsupported result
```

`CfgIndex` may remain as a structural/debug index. It must not be required to
discover the semantic operands of a transfer operation. `SpanNodeIndex` and
`HirCallView` are migration bridges, not part of the final transfer contract.

## Design

### 1. Introduce an owned transfer input

Add a small inference-side representation for a call and its source site. It
should contain the call's HIR identity/span, receiver `ValueId` or receiver
kind, method name, argument operands, block operand, and safe-navigation flag.
It must not contain `ruby_prism::Node` values.

Refactor the call machinery so dispatch can consume this representation:

* positional, keyword, positional-splat, keyword-splat, forwarding, and block
  arguments are read from CFG operands;
* argument types come from `BlockState` values;
* tuple expansion and dynamic-splat behavior remain the existing behavior;
* keyword hash synthesis records the owned key/value types and the call's
  source span without inspecting a Prism keyword hash;
* implicit, explicit, `super`, and `yield` retain distinct semantics; and
* inline and passed blocks resolve through `ClosureId`/`BodyId`, not a parser
  child node.

The old recursive evaluator may keep a separate Prism adapter during the
transition. `BodyTransfer` must use the owned input exclusively. This makes a
call's type result independent of source-span collisions and prevents a
synthetic CFG operation from accidentally selecting the wrong parser node.

### 2. Make value transfer direct

Give `BodyTransfer` an owned `Program` view and use each operation's `ExprId`
for source-sensitive semantics. Transfer must handle:

* `Const`, `Read`, `ReadSpecial`, and `Write` directly from their CFG payload;
* array and hash construction from operand values, including all splat forms;
* inline assertions and source recording through a span/source-site helper;
* pattern tests from the pattern payload and source expression IDs; and
* closure construction as a typed closure value carrying its owned closure/body
  identity.

The transfer host should not call `eval_node` to evaluate an operation's child
expression. Child expressions are already ordered as CFG operations and their
results are in `BlockState`. If a semantic helper still needs a source span,
pass a lightweight owned source site rather than a Prism node.

This is also the point to remove the duplicate array/hash implementation in
which CFG transfer first finds a Prism container and then recursively evaluates
its elements. The CFG operands are authoritative.

### 3. Complete write lowering and transfer

The lowering already exposes attribute and index writes as receiver/argument
evaluation followed by setter calls, and compound/logical writes as
read/test/compute/write sequences. Finish the transfer contract for:

* attribute and index setters with positional, keyword, and splat arguments;
* `&&=` and `||=` for places and dynamic targets;
* binary compound writes for places and dynamic targets;
* post-write value and environment semantics; and
* invalidation/refinement behavior for calls which may mutate a receiver.

There should be no syntax-only special case in `body_can_transfer` for a write
shape whose CFG operations already contain enough information to evaluate it.
If a shape genuinely cannot be represented, extend the CFG operation or block
parameters first; do not widen the result to `T.untyped`.

### 4. Complete call-shape transfer

Remove the current fallbacks for the shapes already represented by
`ArgumentOperand` and `BlockOperand`:

* keyword splats;
* forwarded arguments and forwarded `super`;
* explicit passed blocks;
* inline blocks and block parameter binding;
* safe navigation; and
* `super`/`yield` where the surrounding HIR provides the required owner and
  parameter context.

Each shape needs a fixture that distinguishes a concrete result from an
`T.untyped` fallback. Block calls must also exercise block return types,
optional blocks, and block effects on the caller environment.

### 5. Transfer exceptional control flow

The CFG builder already creates rescue and ensure regions and unwind
successors. Define their abstract-state semantics instead of treating an
unwind edge or `Raise` terminator as an automatic fallback.

The state model must distinguish:

* normal value and environment;
* raised exception type and environment;
* non-local `return`, `break`, and `next`; and
* retry into the active rescue handler.

For every operation which may raise, transfer exceptional state through the
block's `unwind` successor. Rescue matching narrows the exception value and
joins unmatched exceptions with the outer handler. Ensure blocks run exactly
once on normal and exceptional exits, preserve the pending outcome, and then
resume or re-raise it. `retry` targets the active rescue entry with the
correct environment. A handler must not accidentally make a normal path
reachable, and a normal join must not absorb a raised-only path.

Add explicit result fields or an equivalent outcome algebra to the transfer
host; do not encode exceptional behavior by returning `Type::Any`.

### 6. Remove child-body recursive transfer

Once direct operation transfer exists, conditional, loop, `for`, rescue, and
ensure regions should all be ordinary CFG blocks. The specialized
`ConditionalTransfer`, `LoopTransfer`, and `ForTransfer` helpers may remain as
small graph-specific adapters while migration proceeds, but they must consume
owned expression IDs and shared `BlockState` rather than Prism child nodes.

The final body transfer should have one state join implementation. A nested
body or closure is a separate `BodyId` with an explicit summary/input contract,
not an implicit recursive walk of parser children.

## Fallback and diagnostics policy

During migration, a body transfer is transactional:

1. preflight validates that every operation and edge has an owned semantic
   transfer;
2. transfer records into a temporary result context;
3. an unsupported operation returns a classified transfer error; and
4. only a successful body result commits types, diagnostics, dependencies,
   shared reads, and environment updates.

Fallback diagnostics must identify the unsupported HIR/CFG feature and source
span. The counter must be split into at least `unsupported_operation`,
`unsupported_edge`, and `legacy_bridge` so a decreasing total cannot hide a
new semantic fallback. A supported operation must never fall back merely
because its Prism node was not found.

## Migration order

1. Add owned source sites and owned call input; retain the recursive adapter.
2. Convert ordinary calls, keyword calls, splats, and collection transfer to
   owned operands.
3. Convert dynamic/logical/compound writes and closure/block transfer.
4. Unify conditional, loop, and `for` state transfer on owned expression IDs.
5. Implement rescue, retry, ensure, unwind, and non-local outcomes.
6. Delete `SpanNodeIndex` from CFG transfer and make `HirCallView` recursive
   only.
7. Run CFG by default behind a temporary opt-out, then remove the opt-out once
   the differential gates pass.

Each step must add a reduced fixture before changing a Rails or application
result. The fixture should include a concrete `T.reveal_type` or an expected
diagnostic, and the same shape should be exercised with `enable_cfg: true`.

## Acceptance gates

### Semantic parity

For the checker suite, conformance suite, Spoom, Packwerk, and a Rails
component, compare legacy and CFG results for:

* diagnostics, severity, messages, and source spans;
* recorded source types and revealed types;
* normal/raised/terminating flow;
* method return summaries and dependency edges;
* send counts, untyped sends, and untyped-origin categories; and
* shared reads/writes and refinement invalidation.

Differences must be classified as a Typey bug, a missing model, an intentional
Sorbet-compatible gradual behavior, or a real application error. A lower
diagnostic count is not evidence of progress by itself.

### Transfer coverage

The debug report must show:

* zero Prism lookups from the CFG transfer host;
* zero recursive child evaluation from a successfully transferred body;
* zero unclassified legacy fallbacks; and
* only explicitly allowlisted unsupported syntax during the transition.

The allowlist must be source-shape based and reviewed; it must not be a fixed
round limit or a blanket `T.untyped` escape hatch.

### Regression and performance

Run, at minimum:

```text
cargo test --test cfg --test checker --quiet
cargo test --quiet
cargo fmt -- --check
git diff --check
target/release/typey test_repos/spoom --cfg
target/release/typey test_repos/packwerk --cfg
```

Record phase timings separately for discovery/registration, CFG lowering,
transfer, fixpoint rounds, and final diagnostics. Do not treat progress output
as profiling. The completed transfer path should not increase Rails component
time by repeatedly rewalking Prism children; if it does, profile the owned
operation and summary caches before changing convergence policy.

## Exit condition

This spec is complete when CFG transfer can interpret the migrated Ruby/HIR
surface using owned values and explicit control-flow outcomes, the temporary
Prism bridge is gone, remaining fallbacks are classified and intentional, and
legacy/CFG differential runs agree on the accepted repositories. Only then
should the next design step address constraint/evidence propagation or SCC
localization.
