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

The current local gate includes 479 checker tests. The local conformance suite
currently contains 272 generated tests; the newly added CFG fixtures pass
targeted conformance, but the full conformance gate has not been rerun since
the latest transfer changes. The suite
reloads the bundled RBI set per fixture and is correspondingly expensive. A
separate 37-fixture upstream smoke suite was green in the preceding run.
The CFG path is still opt-in because the transfer host retains semantic
bridges in the legacy recursive path: the recursive evaluator still uses Prism
children for exact diagnostics and builtin hooks, while parser-backed callback
contracts and some passed/forwarded-block contexts still need migration.
Ordinary inline callbacks now use an owned HIR contract; optional callable
blocks and nested `&block` forwarding publish concrete return summaries. A
body containing an unsupported operation or an unmigrated callback shape falls
back as a whole.

## Current status (2026-09-12)

The broad transfer surface is complete enough to exercise real repositories.
The release runs below are the current coverage and parity snapshot. Body
counts and coverage denominators include executable source bodies only;
signature declaration bodies and RBI bodies are reported separately as
transfer telemetry.

| Check | Executable source HIR bodies | Unique source bodies transferred | Source coverage | RBI bodies transferred | Transfer visits | Owned calls | Diagnostics |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Spoom | 2,895 | 2,895 | 100.00% | 1 | 9,213 | 35,024 | 3 |
| Packwerk | 1,219 | 1,219 | 100.00% | 1 | 8,084 | 32,959 | 70 |
| Rails ActiveSupport | 4,531 | 4,531 | 100.00% | 1 | 17,142 | 51,808 | 601 |

The legacy differential is retained as historical diagnostic context, not as
the completion criterion:

| Check | Legacy diagnostics | CFG diagnostics | Difference observed |
| --- | ---: | ---: | --- |
| Spoom | 3 | 3 | Exact count and diagnostic parity; the former 3 CFG-only safe-navigation diagnostics are fixed |
| Packwerk | 69 | 70 | 1 distinct CFG-only finding; the count is otherwise exact |
| Rails ActiveSupport | 645 | 601 | 98 CFG-only and 142 legacy-only location/message entries, primarily receiver/model precision differences |

These are differential findings, not silently accepted parity. Spoom has exact
count and diagnostic parity with the legacy path. Packwerk's sole remaining
CFG-only finding is the `T.anything` formatter contract; the earlier
parser-source-map, `Set[...]`, and anonymous `Class.new` findings were fixed in
the owned dispatch path. The owned dispatch path also now keeps `Proc.new` on
the class-object singleton contract, removing the corresponding ActiveSupport
false positives. ActiveSupport still needs category-by-category review of its
generic receiver, framework-hook, and control-flow differences. More legacy
reruns are unlikely to provide useful completion evidence; new work should be
driven by Sorbet/upstream conformance, explicit transfer coverage, and reduced
untyped provenance.

The current Packwerk checkout contains unrelated uncommitted application and
RBI edits, including additional Minitest shim signatures. Its row above is
therefore a measurement of that dirty checkout; the earlier 23-diagnostic
Packwerk row was from the prior clean baseline and is not directly comparable.

Transfer coverage is a body-level ownership metric over distinct bodies:
`unique executable source bodies transferred / executable source bodies`. A
body counts once even if fixpoint inference visits it repeatedly. For example,
Spoom's 100.00% means that all 2,895 of its executable source bodies
completed through the owned CFG transfer path. It does not mean that 100.00% of
lines, sends, types, or diagnostics are covered, and a single transferred body
can contain many calls. Signature declaration bodies and RBI bodies are
excluded from the application coverage denominator and reported separately.
Transfer visits are retained as performance/convergence telemetry, not as
coverage. Bodies outside the attempted owned-transfer set are not counted as
fallbacks; the fallback counters only describe owned bodies that were entered
and then had to return to the legacy evaluator.

The fallback columns are `unsupported_operation / unsupported_edge /
legacy_bridge`; all three repository runs report `0 / 0 / 0`, and all report
zero unsupported HIR handoffs. This is transfer telemetry, not an assertion
that the application has no gradual types: application-level `T.untyped` can
still come from an RBI, an explicit unsafe operation, or a genuinely unresolved
call. The successful-body result now has an explicit rollback boundary for
late, context-sensitive transfer failures; the regression fixture proves that
reports, types, and analyzer state are restored before legacy evaluation.
Remaining implementation work is to finish the remaining passed/forwarded-block
binding cases and remove the parser-facing legacy adapters before making CFG
the default.

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
  owned closure path; optional callable unions ignore their raising `nil` arm,
  and passed `&block` calls publish concrete returns through the CFG fixpoint.
  Ordinary inline blocks remain normally reachable unless the callee's normal
  CFG paths all execute `yield`; in that case non-local callback outcomes can
  terminate the caller path without suppressing diagnostics inside ordinary
  callback bodies.
  Symbol-passed blocks now use owned receiver dispatch, including component
  diagnostics for partially supported union receivers; some forwarded block
  identities still require future binding semantics.
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
* top-level loop and `begin`/`rescue` accounting now stays on the owned CFG
  path: loop exit values and explicit `break`/`next` outcomes are published
  at their owned source spans, and rescue probing does not duplicate a normal
  result when the handler is already reachable.
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
* positional splat arguments now propagate the post-expression CFG block. A
  logical expression inside `*args` therefore cannot re-use the pre-splat
  block and terminate it twice; the regression is covered by
  `cfg_positional_splat_logical.rb`.
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
  still transferring later reveal sites. The loop/begin parity fixtures now
  agree with the recursive evaluator; remaining top-level fallbacks are
  limited to unsupported or legacy-only source-file syntax.

* risk-bearing owned bodies now snapshot and restore mutable analyzer state
  before a late CFG fallback, while ordinary bodies avoid the deep snapshot;
  `cfg_transactional_fallback.rb` verifies that the legacy retry does not
  duplicate or lose recorded products.

* source-file pseudo-expressions including `__FILE__` and `__LINE__`, rescue
  modifiers, backreference reads, Kernel loading calls, lambda-local outcomes,
  explicit mixin receivers, dynamic `alias_method`, the `alias` keyword,
  Enumerable entry contracts, multi-write call/index targets, and nilable
  Array indexing now have owned transfer contracts; each has a focused
  regression test. Inferred methods called from DSL callbacks no longer treat
  an unevaluated provisional `Never` summary as a guaranteed terminating path.

* rescue handlers are analyzed from owned CFG region metadata even when the
  protected call has no statically known raised outcome. The probe is isolated
  at the handler join, seeded from the protected-entry state, and never follows
  retry back into the protected body; handler sends are therefore published
  without leaking handler-local assignments into normal flow.

* inferred methods use `T.noreturn` as a provisional bottom summary during
  fixpoint seeding. A direct recursive CFG call now keeps its normal path while
  that summary is provisional, allowing enclosing expressions to reach their
  widening point. The recursive-container regression converges in two rounds,
  and the combined fixture workload converges in four rounds without a round
  limit.

* reads of ivars with generated writer accessors now account for mutation that
  can occur outside the current method. This prevents constructor literals such
  as `@debug_mode = false` from making later branches unreachable; the owned
  CFG and conformance regression is `cfg_mutable_accessor_ivar.rb`.

* reads of ordinary instance ivars written outside `initialize` now retain the
  possibility of Ruby's default `nil` value, including through generated
  readers. Ivars initialized by `initialize` remain concrete, while singleton
  ivars keep their class-body initialization semantics. The same fixture covers
  both the mutable-writer and lazy-ivar cases.

* optional positional and keyword defaults are evaluated through owned CFG and
  joined into both the method-entry environment and inferred method summary.
  This keeps omitted-argument branches reachable and lets recursive calls
  accept the default's concrete type. The `cfg_optional_default_flow.rb`
  regression covers both the constructor branch and a recursive keyword
  default.

* open inferred parameters keep both truthiness paths reachable without
  erasing a concrete observed type on an impossible falsy branch. `until`
  loops also record their body target separately from their truthy edge, and
  closure callbacks retain the environment captured at their call site. The
  `cfg_open_inferred_parameter.rb` and `cfg_until_loop_flow.rb` regressions
  cover these cases.

* owned method lookup normalizes absolute superclass references when following
  the declaration graph. This preserves inherited RBI methods such as
  `[]`/`[]=` without changing the RBI input; the regression is in
  `resolves_methods_through_absolute_rbi_superclasses`.

The latest release Spoom CFG run has 2,895 executable source HIR bodies and
transferred all 2,895 distinct source bodies plus one RBI body. It made 9,213
body visits and 35,024 calls with zero unsupported-operation fallbacks, zero
unsupported edges, and zero legacy bridges. It reports 3 diagnostics in the
current checkout. The current CFG analysis completes in about 2.26 seconds
internally (3.41 seconds including the CLI repository wrapper) in an
uncontended debug run.

The latest release Packwerk CFG run has 1,219 executable source HIR bodies and
transferred all 1,219 distinct source bodies plus one RBI body. Six `sig` declaration
bodies are reported separately and excluded from application coverage. It made
8,084 body visits and 32,959 calls with zero unsupported-operation, edge, or
legacy-bridge fallbacks. It reports 70 diagnostics in the current dirty
checkout. The `YAML = Psych` standard-library alias remains modeled
through the owned declaration path; runtime `Set[...]` now uses its singleton
RBI contract, and anonymous `Class.new` blocks retain their included methods.
The CFG analysis completes in about 4.23 seconds internally (5.64 seconds
including the CLI repository wrapper) in an uncontended debug run.

ActiveSupport is the current large-component boundary. The current CFG run has
4,531 executable source HIR bodies. After separating
ordinary class-body self types from dynamic missing-method dispatch, preserving
hash shape at recursive widening points, distinguishing generic type
applications from runtime `Constant[]` sends, and evaluating optional defaults
as part of inferred method contracts, it transfers all 4,531 distinct source
bodies plus one RBI body. It made 17,142 body visits and 51,808 calls with zero
unsupported-operation, edge, or legacy-bridge fallbacks, reports 601
diagnostics, and completes in about 5.63 seconds internally (6.49 seconds
including the CLI repository wrapper) in an uncontended debug run.
CFG fallback telemetry now distinguishes unsupported operations, unsupported
edges, and legacy bridges; the migrated ordinary-body path now uses explicit
outcome routing for non-local `return`, `break`, and `next`, including through
ensure regions.

The Ractor storage operators are modeled as class-object methods in both
dispatch paths; this removed seven CFG-only diagnostics without changing the
application code or the RBI.

The two ActiveSupport callbacks that occur after a non-local-return path in
`Rotator#read_message` are now transferred through the generic owned-HIR
callback path. They are not RBI bodies or owned CFG fallbacks, and the release
report now shows complete executable-source coverage.

For historical context, the same release/debug invocation of the legacy path
completed in 5.35s for Spoom, 5.93s for Packwerk, and 5.26s for ActiveSupport.
The CFG path remains slower in this snapshot, especially on Packwerk; these
are end-to-end measurements, not a controlled benchmark or a reason to keep
iterating on legacy parity indefinitely.

As of 2026-09-12, the implementation is therefore not a finished Sorbet
replacement. The checker gate is 479/479, all three repository checks transfer
100% of their executable source bodies with zero measured fallbacks, and
Spoom is an exact application regression check. The full 272-test conformance
gate passed in the latest complete run; the broader suite still has one
workspace failure caused by a dirty fixture whose expected reveal lines were
removed, and the upstream smoke gate still needs a fresh complete run. Remaining
work is primarily Sorbet/upstream behavior coverage, RBI/input-scope handling,
untyped provenance reduction, and performance of the owned transfer path—not
more blind iteration on legacy diagnostic differences.

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
