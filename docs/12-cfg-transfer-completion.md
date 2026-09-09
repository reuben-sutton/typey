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
  before publishing a partial result; and
* transferred rescue, ensure, and retry regions with explicit raised-state
  routing and owned join-value recording.

The current local gates include 22 CFG tests, 12 HIR tests, 424 checker tests,
226 local conformance tests, and a 37-fixture upstream smoke suite. The CFG,
checker, local conformance, and upstream smoke gates pass; the upstream suite
takes about 66 seconds because each fixture reloads the bundled RBI set. The
CFG path is still opt-in because
the transfer host has semantic bridges in the legacy recursive path: the
recursive evaluator still uses Prism children for exact diagnostics and
builtin hooks, while parser-backed callback contracts and some conditional and
loop helpers still evaluate child bodies recursively. Ordinary inline callbacks
now use an owned HIR contract; a body containing an unsupported operation or an
unmigrated callback shape falls back as a whole.

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
owned HIR -> owned CFG -> BlockTransfer -> abstract state/result
                         |-> owned source-site transfer for values, writes, and calls
                         |-> explicit unsupported-body fallback during migration
recursive Prism evaluator -> legacy-only parser adapter
```

The target shape is:

```text
owned HIR -> owned CFG -> BlockTransfer -> abstract state/result
                                      |-> source spans only for recording
                                      |-> explicit unsupported result
```

`CfgIndex` may remain as a structural/debug index. It must not be required to
discover the semantic operands of a transfer operation. `CallNodeIndex` and
`HirCallView` are migration bridges, not part of the final transfer contract.

### Progress in the current iteration

The first modularization steps are now in place:

* `infer/source.rs` owns source-site recording, diagnostics, strictness checks,
  and inline-assertion lookup for CFG paths;
* `infer/source.rs` also owns strictness/RBI source policy and missing-API
  reporting, so diagnostic eligibility is shared by recursive and owned
  transfer without remaining in the analyzer shell;
* `infer/environment.rs` owns the parser-independent abstract environment,
  including local provenance, refinements, self context, and path joins;
* `infer/exceptions.rs` owns the Prism compatibility implementation for
  `begin`/`rescue`/`ensure` and rescue modifiers, keeping legacy unwind
  semantics separate from the analyzer coordinator and owned CFG transfer;
* `infer/case_flow.rs` owns legacy Prism `case`/`case in` evaluation and its
  case-specific narrowing helpers; shared predicate semantics remain in
  `infer/predicate_flow.rs`;
* `infer/framework_hooks.rs` isolates Rails and Active Support callback
  receiver bindings plus Ruby `include`/`extend` hook effects from generic
  call dispatch, while exposing the same contract to recursive and owned
  block inference;
* `infer/intrinsics.rs` owns Sorbet `T.*` intrinsic contracts and implicit
  global/builtin call results, so the coordinator no longer mixes those
  language contracts with transfer and declaration orchestration;
* `infer/assignments.rs` owns HIR assignment transfer across locals,
  attributes, indexes, instance/class/global variables, and constants, while
  retaining the shared send and flow contracts used by both evaluators;
* `infer/registration.rs` owns declaration graph registration, signature
  validation, and attached-class declaration checks, leaving the coordinator
  to orchestrate phases rather than implement declaration policy;
* `infer/cfg_state.rs` owns CFG block state, body context, value joins, and
  pending exception state, leaving `infer/cfg_transfer.rs` focused on operation
  and terminator semantics;
* `infer/keys.rs` owns parser-independent method, storage, and shared-read
  identity keys used across declaration, lookup, fixpoint, and environment
  layers;
* declaration-only accessor, visibility, class metadata, and generic-member
  types now live with `infer/declarations.rs` rather than in the analyzer
  coordinator;
* `infer/method_types.rs` owns parser parameter-shape adaptation, proc/block
  decomposition, overload merging, and callable arity narrowing;
* `infer/method_state.rs` owns the evolving inferred method summary used by
  declaration registration, fixpoint observation, and block contracts;
* `infer/signature_calls.rs` owns signature invocation semantics, including
  generic bindings, argument-shape validation, splat checks, and specialized
  collection return types;
* `infer/signature_calls.rs` also owns inferred-call observation and overload
  selection, keeping method-summary updates beside signature matching;
* `infer/method_lookup.rs` owns receiver/implicit method-key construction,
  ancestor and alias lookup, initializer/struct-constructor support, method
  dependencies, and recursive-call widening;
* `infer/shared_state.rs` owns inferred ivar, constant, class-variable, and
  global storage, including shared-read tracking and the lookup rules used by
  both recursive and CFG evaluation;
* `infer/predicate_flow.rs` owns predicate reachability, path-sensitive
  narrowing, predicate aliases, safe-navigation refinements, and flow
  environment joins shared by legacy and CFG transfer;
* `infer/legacy_eval.rs` owns the recursive Prism evaluator's expression and
  assignment dispatch, leaving the main inference host responsible for
  orchestration and shared state rather than syntax dispatch;
* `infer/legacy_eval.rs` owns recursive statement sequencing and its
  unreachable-flow policy, while `infer/legacy_patterns.rs` owns Prism
  pattern binding and constraints;
* `infer/control_flow.rs` owns the parser-backed loop, `for`, control-value,
  and loop-target transfer retained by the legacy evaluator;
* `BodyTransfer` transfers literals, reads, writes, arrays, hashes, and
  pattern values from CFG/HIR payloads without looking up a Prism node;
* HIR preserves top-level call argument groups, owned source spans, and
  keyword-name spans;
* `infer/call_types.rs` owns the parser-backed call boundary, and CFG dispatch
  receives an `OwnedCallInput` containing the call identity and CFG operands;
  and
* the legacy value dispatcher now transfers fully owned literal/read/array/hash
  trees recursively from HIR source sites, rejecting unsupported children
  before evaluation so it can safely fall back without partial state;
* CFG call shape is first computed as an owned `OwnedCallArguments` value from
  HIR groups and `BlockState` values. Owned keyword-name spans preserve the
  source sites needed for symbol recording; the parser adapter remains only
  for the recursive evaluator's exact diagnostics and builtin hooks;
* `BodyTransfer` no longer depends on `CallNodeIndex`; its calls, argument
  shapes, source sites, and closure identities come from owned CFG/HIR data;
  `HirCallView` remains only as the recursive evaluator's compatibility
  adapter; and
* the `BodyTransfer` call path now consumes only `OwnedCallInput` and owned
  argument shapes. Parser argument materialization remains isolated in the
  recursive call adapter, while CFG builtin and collection contracts consume
  owned types and values directly; and
* `MakeClosure` transfers from its owned `ClosureId` and closure span, so
  closure creation no longer performs a source-span lookup;
* ordinary `while`/`until` bodies now pass CFG preflight, including local
  value-carrying `break` and `next`; block `return`, `break`, and `next` now
  lower to explicit pending outcomes and preserve the enclosing call path;
* simple `for` loops now lower collection iteration and target binding into
  owned CFG operations, preserving the zero-iteration path; unsupported
  multi-target forms remain explicit preflight fallbacks;
* Prism `case` nodes now lower into owned `CaseExpr`/`CaseArm` HIR and transfer
  through the generic CFG path; ordinary value comparisons retain both match
  and no-match paths, while class, `nil`, `true`, and `false` cases perform
  type-based narrowing;
* method-local explicit `return` expressions now pass CFG preflight, join all
  terminal return values and environments, and record enclosing conditional
  expressions on return paths; non-local returns from ordinary blocks use the
  same outcome algebra and run through active ensure regions;
* CFG conditional transfer preserves both predicate edges for inferred local
  variables, matching the recursive evaluator's gradual-flow treatment even
  when a current method summary contains a concrete argument type;
* rescue matching routes raised states through unwind edges, while matched
  handlers consume the pending exception and unmatched exceptions continue to
  the outer handler;
* ensure regions have explicit entry metadata and an `EnsureComplete`
  terminator, so normal, raised, and pending non-local outcomes execute the
  ensure body before continuing, re-raising, or completing the outcome; and
* retry is lowered to the protected body entry, and synthesized calls such as
  compound-assignment sends use owned CFG operands even without a HIR `Call`.
* ordinary inline callback blocks now transfer from owned closure parameters,
  bodies, captured locals, bound receivers, and generic return contracts;
  inline `define_method` and `define_singleton_method` bodies now use the same
  owned closure path; forwarded or passed blocks still require future-method
  binding semantics.
* recursive fallback no longer routes ordinary `if`, `while`/`until`, or `for`
  nodes through a synthetic CFG adapter; owned CFG bodies own branch and loop
  transfer, while unsupported bodies fall back transactionally to the legacy
  evaluator;
* complete owned-body transfer now lives in `infer/cfg_transfer/body.rs`,
  leaving the parent module to coordinate body entry, value/assignment bridges,
  and fallback telemetry while the block worklist owns operation semantics.
* owned value construction, reads, literals, and predicate narrowing now live
  in `infer/cfg_transfer/value.rs`; `patterns.rs` and `preflight.rs` use
  explicit imports instead of inheriting the coordinator's namespace.
* direct owned storage assignment transfer now lives in
  `infer/cfg_transfer/assignment.rs`; the coordinator is limited to call
  bridging, fallback telemetry, and dispatch-level routing.
* the owned-body eligibility walk now lives in `infer/cfg_transfer/preflight.rs`;
  it is a parser-free HIR capability check separate from transfer state and
  inference results.
* pattern reachability, case-test recognition, and environment narrowing now
  live in `infer/cfg_transfer/patterns.rs`, keeping owned predicate semantics
  independent from the worklist coordinator.
* fixpoint seeding, summary worklist scheduling, final publication, and strict
  inference-gap reporting now live in `infer/runner.rs`; `infer.rs` retains
  the shared analyzer state and semantic entry points instead of also owning
  the analysis lifecycle. Pending-return accumulation and summary commits are
  part of that lifecycle boundary as well.
* the remaining HIR-to-Prism lookup helpers for recursive calls and assignment
  children now live in `infer/legacy_bridge.rs`; their `pub(super)` surface is
  an explicit compatibility boundary used by the legacy evaluator and does
  not leak into owned CFG transfer.
* Prism source recording, send classification, parser diagnostics, and type
  deduplication now share `infer/source.rs` with owned `SourceSite` recording;
  the analyzer no longer carries a second source-publication implementation.
* CFG fallback telemetry now records parser call adapters as `legacy_bridge`,
  preflight/operation failures as `unsupported_operation`, and malformed
  worklist successors as `unsupported_edge`, including source spans when the
  fallback originates from an owned body.
* receiver-union/intersection dispatch, resolved invocation, private-call
  checks, overridable-`noreturn` widening, and termination recognition now
  live in `infer/call_dispatch.rs`; `calls.rs` retains argument evaluation and
  the outer call protocol.
* owned CFG calls now have the same semantic layering: `arguments.rs` owns
  HIR/CFG argument materialization, `context.rs` owns `super` and implicit
  global dispatch, `dispatch.rs` owns explicit receiver contracts and
  conservative member-by-member union dispatch, and `outcomes.rs` owns safe
  navigation, callback outcomes, raised-state assembly, and inline
  assertions. The owned call protocol no longer mixes receiver selection with
  final `Eval` construction.
* implicit `raise`, `fail`, `abort`, `exit`, and `exit!` are shared global
  contracts rather than unresolved owned calls. Abrupt-only CFG bodies record
  `T.noreturn` as their expression type while retaining the exception type in
  the separate raised outcome, matching recursive transfer and rescue flow.
* parser-backed `if`/`unless` flow transfer now lives with the loop and `for`
  compatibility routines in `infer/control_flow.rs`; predicate narrowing and
  environment joins remain shared flow services rather than coordinator code.
* a fully representable top-level HIR body now attempts owned CFG transfer
  before the recursive Prism statement walker; definitions and unsupported
  top-level syntax still fall back as a whole through the transactional
  preflight boundary.
* the compatibility assignment adapter no longer evaluates an unsupported RHS
  through `eval_node`; it declines the owned assignment path before publishing
  state, leaving the complete assignment to the recursive evaluator.
* CFG no longer reroutes ordinary calls through a `HirCallView` adapter;
  `HirCallView` is recursive-only, owned calls increment the CFG transfer
  counter directly, and migrated CFG runs report zero `legacy_bridge`
  fallbacks;
* index assignment preflight now preserves positional, keyword, and splat
  operands for the synthesized `[]=` call; ordinary nominal `[]` sends also
  fall back from callable shorthand to regular receiver dispatch when the
  receiver is not proc-like.
* owned callable dispatch now handles unary negation and explicit `Proc` /
  `BoundProc` `call`/`[]` operations from CFG values, including unioned
  callable receivers, argument checking, and optional RBS block contracts;
  the optional-block and union-callable fixtures verify that CFG and recursive
  transfer publish identical source types. Unary negation keeps its boolean
  result for flow narrowing without recording an extra internal call type at
  the operand span.
* interpolated strings, regular expressions, symbols, xstrings, and
  match-last-line expressions now lower to owned HIR/CFG construction
  operations with no child Prism evaluation; their conformance expectations
  are checked against the same source spans.
* `defined?` now lowers its operand into owned HIR/CFG operations. Operand
  sends and inferred values remain visible for accounting, while only the
  probe's ordinary diagnostics are suppressed, matching the recursive
  evaluator's behavior.
* `&&` and `||` now lower to owned short-circuit CFG branches and a value join.
  The transfer layer carries truthiness through nested unary negation and
  carries facts from a composite predicate into the normal path after an
  `unless`/`if`, preserving concrete receiver types without a parser fallback.
* method, class, module, and singleton-class declarations now lower their
  owned runtime operands and transfer nested declaration bodies through the
  same CFG worklist. Method summaries, class-body effects, superclass
  expressions, singleton receivers, and Struct constructor field metadata no
  longer require a declaration-shaped parser fallback.
* top-level terminating calls preserve the legacy `T.noreturn` aggregate while
  still transferring later reveal sites, and the loop/begin parity fixtures
  now agree with the recursive evaluator. The remaining top-level fallback is
  isolated to a source-file body whose legacy statement accounting still
  needs to be represented directly in CFG.

* source-file pseudo-expressions including `__FILE__` and `__LINE__`, rescue
  modifiers, backreference reads, Kernel loading calls, lambda-local outcomes,
  explicit mixin receivers, dynamic `alias_method`, the `alias` keyword,
  Enumerable entry contracts, multi-write call/index targets, and nilable
  Array indexing now have owned transfer contracts; each has a focused
  regression test. Inferred methods called from DSL callbacks no longer treat
  an unevaluated provisional `Never` summary as a guaranteed terminating path.

The latest release Spoom CFG run compiled 58,854 HIR bodies and transferred
8,670 bodies and 34,184 calls with zero unsupported-operation fallbacks, zero
unsupported edges, and zero legacy bridges. It reports the same 3 diagnostics
as the recursive path; the CFG run takes 7.23 seconds including repository
checking versus 7.08 seconds recursively, and reaches final convergence in
four worklist rounds. The three shared findings are a real nilable `Time`
argument, an impossible branch under the vendored Prism model, and a nilable
array comparison result.

The remaining bridges are deliberate and measurable: the recursive evaluator's
call adapter still needs parser nodes for exact argument diagnostics and
builtin hooks, while forwarded or passed blocks supplied to
`define_method`/`define_singleton_method` still require future-method binding
semantics in some receiver contexts. On the latest Packwerk regression run,
the owned path compiled 73,396 HIR bodies, transferred 8,886 bodies and
38,024 calls, and reached convergence in four rounds with zero unsupported
operation, edge, or legacy-bridge fallbacks. Its 22 diagnostics match the
recursive path exactly. The `YAML = Psych` standard-library alias is modeled
through the owned declaration path, so the earlier YAML diagnostics are gone.
The remaining Packwerk difference is accounting: the owned path has 119
application sends without a recorded type and records 14,382 types, while the
recursive path records all 1,578 application sends and 41,773 types. This is
a publication/send-tracking gap, not evidence that the owned path is more
correct.

The latest full ActiveSupport run is the current large-component boundary:
27,099 HIR bodies were compiled and 14,247 bodies and 46,255 calls transferred
across five worklist rounds. Static `undef` is now an owned operation, leaving
zero unsupported-operation records, zero unsupported-edge fallbacks, zero
legacy bridges, and zero unsupported HIR handoffs in this component. The CFG
run reports 568 diagnostics and 38,834 recorded types in 214.4 seconds; the
fresh legacy recursive run reports 689 diagnostics and 43,378 recorded types
in 212.6 seconds. Of the diagnostic sets, 501 findings are shared, 188 are
recursive-only, and 67 are CFG-only. Runtime is therefore approximately at
parity, but the diagnostic and type-publication differences still require
differential classification. CFG is not yet a replacement: the remaining work
is primarily ActiveSupport differential analysis, owned send/type publication,
the remaining parser-backed call and passed/forwarded-block bridges, and
making CFG the default only after those gates agree.
CFG fallback telemetry now distinguishes unsupported operations, unsupported
edges, and legacy bridges; the migrated ordinary-body path now uses explicit
outcome routing for non-local `return`, `break`, and `next`, including through
ensure regions.

As of 2026-09-09, the implementation is therefore in the final parity phase,
not at the exit condition. The checker gate is 424/424, Spoom and Packwerk
diagnostics agree exactly, and the CFG transfer surface has zero measured
fallbacks on all three repository checks. What remains is not broad CFG
coverage: it is reconciling ActiveSupport's 255 non-shared diagnostics,
restoring the missing owned type publications, and then rerunning the full
differential gates before retiring the recursive path.

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
5. Implement rescue, retry, and ensure unwind routing. Non-local `return`,
   `break`, and `next` outcome routing is now explicit; the remaining work is
   to retire the parser-backed call and DSL bridges.
6. Keep parser call views recursive-only and remove synthetic parser-backed CFG
   adapters as their owned body equivalents become complete.
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
