# Interprocedural summaries and SCC-aware convergence

This is the next architectural phase after
`docs/12-cfg-transfer-completion.md`. The CFG transfer phase answers:

> Given one body and an abstract input state, what happens along every CFG
> path?

This phase answers:

> How do bodies exchange stable information, and how do recursive bodies reach
> a precise fixed point without repeatedly replaying the whole source tree?

The existing checker already has a method worklist, but its interprocedural
state is narrower than the transfer state. `FixpointState` stores pending
return type/termination pairs, reverse caller edges, and shared-value reader
edges. `observe_call` also mutates inferred parameter evidence in
`MethodState`. Each round replays the source root and filters evaluation to
the methods scheduled for that round. There is no forward callee edge, no
transactional replacement of a method's outgoing dependencies, and no SCC
representation.

The result is correct enough for the current differential path, but it makes
recursive convergence and performance difficult to reason about. A method
summary must become an explicit product of the body transfer, and the outer
solver must operate on a dependency graph rather than rediscovering callers
by replaying the root.

## Goals

1. Define a complete, comparable method-summary value.
2. Separate body-local CFG state from interprocedural summaries.
3. Track call and shared-state dependencies in both directions and replace
   stale outgoing edges safely.
4. Solve recursive methods by strongly connected component (SCC), with a
   deterministic local worklist.
5. Preserve concrete information and existing gradual-typing distinctions;
   convergence must not be achieved by replacing uncertainty with
   `T.untyped`.
6. Publish diagnostics and source types only after summaries stabilize.
7. Measure body evaluations and convergence directly, rather than inferring
   performance from round counts.

## Non-goals

This phase does not introduce a general constraint language or evidence graph.
It does not change the type lattice, Sorbet feature semantics, RBI loading, or
framework models. It also does not introduce call-site specialization as a
new precision mechanism. If context-sensitive summaries are later required,
they get a separate design after the declaration-level protocol is stable.

## Current-to-target architecture

The current outer loop is approximately:

```text
replay root
  -> evaluate selected method bodies
  -> mutate pending return types and caller edges
  -> commit all return changes
  -> schedule callers
repeat
final root replay with reporting
```

The target is:

```text
register declarations and initial call graph
  -> partition reachable methods into SCCs
  -> solve each SCC from settled external summaries
  -> publish changed summaries to dependent SCCs
  -> final reporting pass over stable summaries
```

CFGs and body-level transfer results remain cached by `BodyId`. The solver
should invoke transfer for a scheduled body directly; it must not walk the
combined source root merely to rediscover that body's definition.

## Summary model

Introduce an explicit summary type at the boundary between body transfer and
the declaration/fixpoint solver. The exact Rust names may differ, but the
fields must have these semantics:

```rust
struct MethodSummary {
    method: MethodKey,
    input: MethodInput,
    normal_return: Type,
    return_terminates: bool,
    abrupt: OutcomeTypes,
    effects: EffectSummary,
    dependencies: DependencySummary,
}

struct MethodInput {
    receiver: Type,
    positional: Vec<Type>,
    keywords: BTreeMap<String, Type>,
    block: BlockInput,
}

struct EffectSummary {
    shared_reads: BTreeSet<SharedKey>,
    shared_writes: BTreeSet<SharedKey>,
    instance_writes: BTreeSet<String>,
}

struct DependencySummary {
    callees: BTreeSet<MethodKey>,
    shared_reads: BTreeSet<SharedKey>,
}
```

The implementation may retain additional fields, such as flow categories or
untyped-origin evidence, but it must not hide them inside mutable global
state. The summary is the candidate result of one complete body evaluation.

### Summary rules

* Explicit signatures remain authoritative. Their summary is derived from the
  declared signature and overload/block contract rather than inferred from a
  body.
* Inferred methods retain the existing argument-observation behavior, but the
  observed input is committed as part of the method's summary transaction.
* Generic substitution, `T.attached_class`, `T.self_type`, overload choice,
  and block signature substitution happen at the call boundary. The summary
  stores the result for the resolved method, not an erased `T.untyped` form.
* A normal return, a `T.noreturn`/terminating result, and raised/non-local
  outcomes remain distinct. A method which can return normally and raise must
  not be summarized as only `T.noreturn` or only its normal type.
* Effects are conservative joins. A body that may write a shared key or
  instance variable must not cause callers to retain stale facts across the
  call.
* A summary with no evidence is represented by the existing gradual top
  values. It must not manufacture a concrete type, but a concrete type proven
  by a body or declaration must not be widened merely because the method is
  in a cycle.

Initially, summary identity remains declaration-level (`MethodKey`). The
`MethodInput` fields document and stabilize the existing inferred parameter
contract; they do not create one summary per call site. Any later move to
context-sensitive summaries must specify cache keys, specialization limits,
and invalidation separately.

## Transactional body evaluation

Body transfer produces a candidate summary and a local dependency/effect
record. It must not mutate the committed graph or method state while it is
still evaluating. The solver performs this transaction:

1. snapshot the method's committed input and external summaries;
2. run its cached CFG body;
3. collect the candidate summary, diagnostics/types when reporting, outgoing
   callees, and shared reads/writes;
4. compare the candidate with the committed summary using field-specific join
   rules; and
5. commit the summary and replace its outgoing dependency/effect edges only
   after the evaluation succeeds.

If transfer falls back or fails, no partial return type, diagnostic, type
record, or dependency edge may be committed. The fallback remains explicit
and classified under the CFG transfer policy.

## Dependency graph

Maintain both directions for every dependency:

```text
caller -> callees
callee <- callers
```

For shared state, maintain the equivalent reader/writer relationships:

```text
method -> shared reads/writes
shared key -> readers and writers
```

When a body is reevaluated, collect a fresh outgoing set. Remove the old
edges for that body before installing the new set. This matters when method
resolution becomes more precise, a branch becomes unreachable, a dynamic
call disappears, or a shared read is no longer on a reachable path. Stale
edges cause unnecessary work and can make convergence appear to require more
information than it does.

Use a synthetic root node for top-level calls and shared reads, or model root
dependencies explicitly. The root must not be treated as an ordinary method
body when computing inferred method summaries.

Unresolved dynamic dispatch records the existing gradual fallback provenance,
but does not invent a dependency on every method with the same name. If a
conservative dependency is required by a specific model, represent it as an
explicit dependency kind and measure its fan-out.

## SCC discovery

Build SCCs over the reachable method dependency graph after registration and
the initial call-discovery pass. Use Tarjan or Kosaraju with stable
`MethodKey` ordering so component IDs and traces are deterministic.

The condensation graph is acyclic. If an edge is represented as
`caller -> callee`, solve the condensation graph in callee-first topological
order. A component must be recomputed when:

* a method enters or leaves the reachable graph;
* an outgoing dependency set changes across a committed body evaluation; or
* a shared-state dependency connects it to a changed component.

The implementation may defer graph repartitioning until the current local
solve finishes, but it must mark the affected components and recompute before
using the graph as settled. It must not rely on a fixed number of global
rounds to compensate for a changing graph.

## SCC-local solver

For each SCC:

1. import committed summaries from already-settled external callees;
2. seed each method with its previous summary, or the least useful summary
   allowed by the existing inference lattice;
3. enqueue every method whose input or external dependency changed;
4. evaluate one method body through cached CFG transfer;
5. join the candidate into the method's summary;
6. enqueue intra-SCC callers when a summary field changes; and
7. continue until the SCC has no changed summaries, dependencies, or shared
   effects.

Only strict changes enqueue another evaluation. The queue and component order
must be deterministic.

The solver must not use an arbitrary round limit. If an abstract domain can
form an infinite ascending chain, define an explicit widening for that field
and test it independently. Existing recursive-container widening should move
behind this summary boundary and preserve the most precise concrete finite
upper bound available; it must not fall back to `T.untyped` simply to stop a
cycle.

When an SCC stabilizes, publish changed summaries to predecessor components
and shared-state readers. A component with no summary change but a changed
outgoing dependency set still invalidates graph topology and must be handled
before global settlement.

## Shared-state convergence

Shared reads and writes participate in the same dependency protocol as calls.
For each `SharedKey`:

* maintain its committed abstract value and version;
* record which methods read it and which methods write it;
* join writes monotonically according to the existing type rules; and
* reschedule readers only when the value or relevant effect summary changes.

Instance-variable facts need an explicit owner/environment key. A write to an
instance variable on one receiver class must not invalidate every unrelated
class, while a framework operation that can mutate arbitrary instances must
declare that broader effect.

The final reporting pass uses the settled shared values and does not mutate
them. Any remaining provisional or unknown state must be visible in the
diagnostic/metrics classification rather than silently discarded.

## Publication and reporting

There are three distinct phases:

1. **Discovery:** register declarations, lower/cache HIR and CFG, and discover
   initial call/dependency edges without publishing diagnostics.
2. **Solve:** evaluate summaries and shared values until the dependency graph
   and all reachable SCCs stabilize. Do not retain transient source types or
   diagnostics from this phase.
3. **Report:** evaluate the root and required bodies once using committed
   summaries, publishing diagnostics, inferred source types, send metrics, and
   untyped provenance.

The report phase must not change a settled summary. If it does, that is a
solver bug and should be asserted or reported as a failed differential gate.

## Migration plan

1. Extract `MethodSummary` and `DependencySummary` from the current
   `MethodState`, `pending_returns`, and dependency maps without changing
   scheduling.
2. Add forward callee edges and transactional edge replacement while retaining
   the existing global worklist.
3. Add summary/effect comparison and versioned shared values.
4. Implement deterministic SCC discovery and report component boundaries in
   debug output, but keep the old scheduler as a differential mode.
5. Solve acyclic components directly from settled callees.
6. Move recursive methods to the SCC-local worklist and migrate recursive
   widening to explicit summary fields.
7. Remove root replay from fixpoint rounds; retain one final reporting pass.
8. Compare the new solver with the old one, then make it the default.

Each stage must be independently revertible and committed separately. No
application source or RBI should be modified to make the new solver agree.

## Fixtures and regression tests

Add focused fixtures for:

* a caller defined before its callee;
* mutual recursion with a concrete base case;
* recursive containers whose summary requires widening;
* recursion with both normal and terminating branches;
* changed call resolution which removes a stale dependency edge;
* shared reads/writes that invalidate only affected readers;
* generic methods, `T.attached_class`, `T.self_type`, overloads, and block
  signatures crossing a method boundary; and
* dynamic dispatch which remains gradual without scheduling every same-named
  method.

For each fixture, compare legacy and new scheduling for diagnostics, revealed
types, return summaries, flow outcomes, send counts, untyped-origin
categories, and dependency traces. Add a checker assertion for each bug found,
not only a final diagnostic count.

## Acceptance gates

The new solver is ready when:

* `cargo test --quiet`, checker/conformance tests, Spoom, Packwerk, and a
  Rails component agree with the legacy solver after classification;
* no committed summary changes during the final reporting pass;
* every reachable method has explicit forward and reverse dependency edges;
* stale edges are removed when a body's outgoing dependencies change;
* SCC order, membership, and local evaluation are deterministic;
* no arbitrary global round limit is required;
* recursive widening is explicit, tested, and never a blanket `T.untyped`
  escape; and
* debug metrics show body evaluations, SCC count/size, summary changes,
  shared-key invalidations, dependency replacements, and time per phase.

The primary performance comparison is body-transfer evaluations and elapsed
time for registration, solve, and report. A smaller diagnostic count is not a
success criterion unless the removed findings are classified as correct.

After this phase, a separate constraints/evidence spec can address richer
cross-expression proof propagation. It should build on stable summaries and
SCC convergence rather than trying to solve interprocedural scheduling and
type evidence simultaneously.
