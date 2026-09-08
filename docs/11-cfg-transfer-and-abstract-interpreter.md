# Post-CFG step: transfer and abstract interpretation

The HIR and CFG models are now present. The next step is to make the CFG
executable by adding a block-oriented abstract interpreter. This phase moves
evaluation of control flow out of the recursive Prism evaluator while keeping
the existing type lattice, method summaries, dispatch, and fixpoint scheduler.

This is intentionally not yet a general constraint solver or an evidence
graph. The first goal is a behavior-preserving execution engine for the CFG.

## Scope and boundaries

The pipeline for this phase is:

```text
owned HIR → owned CFG → block transfer → existing summaries/worklist
```

The transfer layer may use the existing declaration and type APIs, but it must
not parse Prism nodes or rediscover control flow. During migration, a narrow
temporary adapter may map a CFG operation back to its HIR expression for
legacy call handling. That adapter must be isolated and removed before the CFG
path becomes the default.

The following remain outside this phase:

* replacing method summaries with a general constraint language;
* changing the type lattice;
* adding framework-specific CFG operations;
* changing Sorbet or RBS semantics;
* changing the meaning of `T.untyped`, `T.anything`, or `T.noreturn`.

## Analysis state

CFG construction is pure. Transfer owns the mutable abstract state for one
body evaluation:

```rust
struct BlockState {
    values: Vec<Option<Type>>,
    environment: Environment,
    flow: Flow,
}

struct BodyContext {
    method: Option<MethodKey>,
    self_type: Type,
    parameters: Parameters,
    strictness: Strictness,
}

struct BodyResult {
    return_type: Type,
    return_terminates: bool,
    normal: Option<BlockState>,
    diagnostics: Vec<Diagnostic>,
    types: Vec<InferredType>,
}
```

`BlockState` is a dataflow value, not a method summary. A method summary is
still stored by the existing declaration/fixpoint layer and is updated only
after a body evaluation has completed. This preserves the current
synchronous-summary behavior and prevents source order from affecting
inference.

Unreached blocks are represented by `None`, never by `T.untyped`. A reached
block is joined with a predecessor using the existing environment and type
lattice rules. A state change is monotone with respect to those joins; an
unchanged state must not reschedule the block.

## Operation transfer

Every `Operation` has one transfer function. It consumes the current state and
updates the result slot when the operation produces a value.

| CFG operation | Transfer behavior |
| --- | --- |
| `Const` | Use the existing literal-type rules. |
| `Read` | Read the corresponding local, ivar, class variable, global, or constant. Register shared reads. |
| `ReadSpecial` | Resolve `self`, numbered parameters, `it`, and back-references using the body context. |
| `Write` | Update the place, preserve provisional/concrete write rules, and return the assigned value. |
| `Call` | Evaluate the preserved receiver/argument shape, resolve dispatch, check the call, bind the block, and register method dependencies. |
| `MakeClosure` | Produce a callable value referring to the closure body without executing it. |
| `BuildArray` | Evaluate elements left to right and preserve tuple/open-array behavior. |
| `BuildHash` | Evaluate pairs and splats with the existing key/value inference. |
| `PatternTest` | Produce a Boolean result and expose the predicate used by successor refinement. |
| `Unsupported` | Use the explicit legacy handoff during migration; preserve its span and do not invent a concrete type. |

Call transfer must continue to distinguish implicit, explicit, `super`, and
`yield` calls, positional and keyword splats, forwarding, safe navigation,
inline blocks, and passed blocks. These are semantic inputs to dispatch, not
just a list of already-inferred argument types.

The transfer layer may record diagnostics only when running the final
reporting pass. Seed and fixpoint passes update summaries and dependencies but
must not publish transient diagnostics or node types.

## Terminator transfer

Terminators propagate state to successor blocks:

* `Jump` substitutes the supplied values into the target block parameters.
* `Branch` clones the state, applies truthy/falsy predicate refinement, and
  sends each state to its corresponding successor.
* `Return` contributes a normal return value and termination fact to the body
  result, then stops that path.
* `Raise` contributes an abrupt exception outcome and follows the active unwind
  edge when one exists.
* `Unreachable` contributes nothing.

The existing `Flow` and `OutcomeTypes` types remain the source of truth for
normal, returned, broken, continued, retried, and raised outcomes during the
migration. The CFG engine should adapt to them before attempting to redesign
abrupt-flow representation.

## Block worklist

Each body is evaluated with a local block worklist:

```text
state[entry] = initial body state
queue = [entry]

while queue is not empty:
    block = queue.pop()
    result = transfer(block, state[block])
    for successor in result.successors:
        joined = join(state[successor], successor.incoming_state)
        if joined changed:
            state[successor] = joined
            queue.push(successor)
```

The queue must be deterministic for reproducible diagnostics and debugging.
Use block IDs as the stable ordering key. A loop is therefore solved by the
same monotone worklist mechanism as an ordinary join; no arbitrary iteration
limit may be added.

Block compilation is cached by `BodyId`. A method-summary change causes the
body to be reinterpreted with the new input summaries, not reparsed or
re-lowered. The outer method worklist remains responsible for scheduling
dependent bodies until summaries stabilize.

## Control-flow cases

### Conditional joins

The branch transfer must reuse the current predicate machinery. It must carry
facts such as non-nil, truthiness, non-empty arrays, predicate aliases, and
case exclusions on the edge. At the join, retain only facts valid on every
normal predecessor.

An absent `else` contributes an explicit `nil` path. A path ending in `Return`,
`Raise`, or another abrupt outcome contributes no normal value to the join.

### Loops

Loop headers receive the joined entry and back-edge states. `break` jumps to
the loop exit and supplies the loop result; `next` jumps to the condition or
iteration header. The existing loop widening and non-empty-array behavior
must be preserved exactly.

### Rescue and ensure

The active `unwind` successor receives an exception value and enters the
corresponding rescue handler. Rescue matching and rescue-reference binding
reuse the current exception type rules. Normal completion follows `else` when
present. Both normal and exceptional paths execute `ensure` before leaving
the protected region. `retry` returns to the rescue entry.

## Method and shared-state integration

The transfer layer must preserve the current fixpoint interfaces initially:

* a `Call` records the resolved callee in `method_callers`;
* method return values are accumulated in `pending_returns`;
* reads register in `shared_readers`;
* writes mark the relevant `SharedKey` changed;
* dynamic include, extend, accessor, and framework models use the same
  declaration APIs as the legacy evaluator.

The CFG interpreter must evaluate only the scheduled body when
`filter_method_bodies` selects a method. It must not enter the combined source
root merely to rediscover that method.

Top-level code remains a CFG body as well. Its state seeds method calls and
shared values, then the final reporting pass runs it once with settled
summaries.

## Migration stages

1. Introduce `BlockState`, `BodyContext`, and the local block worklist without
   changing the default path.
2. Transfer `Const`, `Read`, `Write`, `MakeClosure`, and ordinary `Call`
   operations through the existing inference APIs.
3. Transfer branch/join edges and compare predicate refinements with the
   recursive evaluator.
4. Transfer loops, `break`, and `next`.
5. Transfer rescue, `retry`, `raise`, unwind edges, and `ensure`.
6. Remove the temporary Prism child-node adapter and make CFG transfer the
   default.
7. Only after this is stable, evaluate whether constraints, evidence, or SCC
   scheduling are needed for the remaining fixpoint costs.

Each stage must leave the legacy path available for differential testing until
the corresponding construct has coverage.

## Tests and acceptance criteria

Add `tests/analysis.rs` or an equivalent focused suite for:

* block-state joins and unreachable predecessors;
* left-to-right calls and all argument shapes;
* local and instance-variable reads/writes;
* safe navigation and nilability;
* predicate narrowing and case exclusions;
* loops, loop-carried state, `break`, and `next`;
* rescue matching, exception references, `retry`, and `ensure`;
* method-summary changes across multiple CFG passes.

For every migrated fixture, compare legacy and CFG paths for:

* diagnostics and source locations;
* final inferred types and send flags;
* abrupt-flow outcomes;
* untyped origins;
* method and shared-state dependency edges.

The phase is complete when CFG transfer is the default implementation for all
supported HIR bodies, no supported operation requires Prism lookup, and the
checker suite, conformance suite, Spoom, Packwerk, and a release-mode Rails
component retain their classified behavior and performance baseline.
