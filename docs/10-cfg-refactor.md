# CFG refactor specification

The owned HIR now exists in `src/hir/`. The next refactor lowers each HIR
body into a control-flow graph (CFG) and moves expression evaluation from the
Prism-oriented recursive evaluator to CFG transfer functions.

This is an inference refactor, not a new type-system feature. It must preserve
all existing diagnostics, inferred types, source locations, send metrics,
method-summary changes, and gradual-typing behavior.

## Goals

The CFG must make these facts explicit:

* evaluation order;
* values produced by expressions;
* local, ivar, constant, and other storage reads and writes;
* normal control-flow joins;
* `return`, `raise`, `break`, `next`, and `retry` transfers;
* rescue and ensure edges where they affect analysis;
* the exact source span responsible for each operation.

The CFG must not contain inferred `Type`s, `Environment`s, diagnostics, or
Rails-specific operations. Those belong to the analyzer and its models.

The first implementation should use a normal value-flow graph. It should not
require full SSA conversion. Block-entry environments can continue to use the
existing lattice joins; `ValueId`s only identify expression results within a
body.

## CFG data model

Add a `src/cfg/` module with body-local IDs:

```rust
struct Cfg {
    body: BodyId,
    entry: BlockId,
    blocks: Vec<BasicBlock>,
}

struct BasicBlock {
    id: BlockId,
    parameters: Vec<BlockParameter>,
    operations: Vec<Operation>,
    terminator: Terminator,
    unwind: Option<BlockId>,
}

struct Operation {
    span: Span,
    result: Option<ValueId>,
    kind: OperationKind,
}
```

`BlockParameter` is used for values that arrive from predecessors, such as a
joined expression result or the exception value entering a rescue handler.
`unwind` is the active exception successor for operations in the block. The
builder must split blocks when the active rescue or ensure region changes.

Places represent storage locations, not method calls:

```rust
enum Place {
    Local(LocalId),
    InstanceVariable(Name),
    ClassVariable(Name),
    Global(Name),
    Constant(ConstantPath),
}
```

Attribute and index targets are not `Place`s. They lower to receiver/argument
evaluation followed by reader and writer calls, because their evaluation order
and dispatch are observable.

## Operations

The minimum operation vocabulary is:

```rust
enum OperationKind {
    Const { value: Literal },

    Read { place: Place },
    Write { place: Place, value: ValueId },

    Call {
        receiver: ReceiverOperand,
        name: Name,
        arguments: Vec<ArgumentOperand>,
        block: Option<ClosureId>,
        safe_navigation: bool,
    },

    MakeClosure { closure: ClosureId },

    BuildArray { elements: Vec<ArrayOperand> },
    BuildHash { elements: Vec<HashOperand> },

    PatternTest { value: ValueId, pattern: Pattern },

    Unsupported { kind: Name },
}
```

The result field on `Operation` holds the value produced by operations such as
`Const`, `Read`, `Call`, and collection construction. A write also produces
the assigned value through the surrounding expression's result handling.

Calls must preserve the HIR distinctions:

* implicit, explicit, `super`, and `yield` dispatch;
* positional, splat, keyword, keyword-splat, and forwarded arguments;
* inline closure IDs versus passed block expressions;
* safe-navigation behavior.

`Call` is the generic operation used for operators, accessors, `[]`, dynamic
dispatch, framework APIs, and Sorbet helpers. No Rails operation is added to
the CFG vocabulary. For example, `config/routes.rb` still contains an
ordinary call whose model later supplies the `Mapper` block receiver.

`Unsupported` is transitional only. It preserves the source span and gives
the legacy evaluator an explicit handoff point. It must never be interpreted
as a concrete value or silently converted to `T.untyped`.

## Terminators

The normalized CFG terminators are:

```rust
enum Terminator {
    Jump {
        target: BlockId,
        arguments: Vec<ValueId>,
    },

    Branch {
        condition: ValueId,
        truthy: BlockId,
        falsy: BlockId,
    },

    Return(Option<ValueId>),
    Raise(ValueId),
    Unreachable,
}
```

`break` and `next` lower to jumps to loop exit and loop-header blocks,
respectively, passing their result through block parameters. `retry` lowers to
the appropriate rescue entry. They should not remain as Ruby-specific
terminators after CFG construction.

## Lowering rules

CFG construction is a pure transformation from one HIR body to one CFG. It
does not resolve methods or infer types.

### Sequences and values

Lower sequence expressions in source order. The value of a sequence is the
value of its last normally completing expression. If an expression transfers
control, do not lower subsequent expressions into the same reachable block.
An empty sequence produces `nil`.

### Calls and blocks

Evaluate an explicit receiver before arguments, then arguments left to right,
then emit the call operation. Preserve argument shape rather than flattening
splats into a guessed list. A closure is created as a `ClosureId`; its body is
not executed when the block is constructed.

`super` and `yield` remain distinct call targets. The analyzer will resolve
them using the current method and environment context.

Safe navigation must not unconditionally invoke the method on a possibly nil
receiver. Lower it to a nil test, a nil result path, and a call path, followed
by a join. The call path retains the original call span.

### Assignments

`Set` evaluates the right-hand side and writes it to the target.

`And` and `Or` lower to a target read, a truthiness branch, and a conditional
right-hand-side write:

```text
read old
branch old -> existing_value / evaluate_rhs
evaluate_rhs: write target, rhs
join result
```

Binary assignment evaluates the target read and right-hand side, emits the
operator call, writes the result, and returns that result. Attribute and index
assignments evaluate their receiver and arguments exactly once before the
reader/writer calls are emitted.

### Conditionals and joins

An `if`, `unless`, or case arm gets distinct blocks for each path and a join
block for normally completing paths. The branch edge carries the predicate
fact used by the later analyzer. The join operation/state uses the existing
`Environment::join` semantics: facts are retained only when valid on every
incoming normal path.

An absent `else` is an explicit `nil` path. A path ending in `Raise`,
`Return`, or another non-normal transfer does not contribute a normal value to
the join.

### Loops

Create a header block, condition block, body block, and exit block. The back
edge joins the loop-carried environment with the entry state. `while` and
`until` invert the condition edge as appropriate. `for` preserves its Ruby
iteration-variable and scope behavior; it must not be reduced to an ordinary
collection call unless that is already the existing semantic model.

### Rescue and ensure

Lower a `begin` body with its current exception handler in `unwind`. Rescue
clauses become handler blocks that test the incoming exception and either
continue with the clause body or transfer to the next handler. A handled
exception enters the rescue body with the reference local bound to the
exception type.

Normal completion goes through `else` when present. Both normal and exceptional
paths pass through `ensure` before leaving the protected region. `retry`
returns to the rescue entry, not the ordinary loop header.

## Analyzer transfer functions

The CFG builder is syntax-only. A separate transfer pass evaluates operations
with the existing inference machinery:

* `Read` and `Write` use the current ivar, local, constant, class-variable,
  and global models;
* `Call` uses existing argument-shape handling, dispatch, block binding,
  generic substitution, and dependency recording;
* `PatternTest` invokes existing predicate and narrowing logic;
* block joins use the current flow lattice;
* method-summary updates continue to use the existing fixpoint worklist at
  first.

The transfer pass returns a normal value fact plus abrupt outcomes. It may
record diagnostics, but the CFG itself remains reusable across fixpoint
rounds. Compiling a body must not be repeated merely because a method summary
changed.

The first migration should split `MethodState` conceptually into its existing
declaration data and its mutable summary, but it need not redesign the
summary solver yet.

## Migration plan

1. Add CFG IDs, blocks, operations, terminators, and a pure HIR-to-CFG builder.
2. Add structural CFG tests for calls, `if`, `||=`, loops, and rescue.
3. Compile every supported HIR body once and retain the legacy evaluator as a
   differential path.
4. Move calls and assignments to CFG transfer functions first.
5. Move conditionals, loops, rescue, and ensure.
6. Compare legacy and CFG results, then remove the legacy path once all HIR
   variants are covered.

During the migration, unsupported HIR nodes must be reported in debug output
and tested explicitly. The fallback must preserve current behavior and must
not suppress diagnostics or replace concrete evidence with `T.untyped`.

## Tests and acceptance criteria

Add `tests/cfg.rs` covering:

* left-to-right call evaluation and all argument shapes;
* inline and passed blocks;
* `super`, `yield`, and forwarding;
* safe navigation;
* plain, compound, attribute, and index assignments;
* branch joins and unreachable paths;
* loop back edges and `break`/`next`;
* rescue matching, rescue references, `retry`, and `ensure`.

The refactor is complete only when:

1. CFG construction consumes owned HIR and no Prism node;
2. every supported HIR body has an explicit CFG;
3. CFG transfer replaces direct AST evaluation for calls and assignments;
4. diagnostics, inferred types, source spans, send metrics, and untyped
   provenance match the legacy path;
5. `cargo test --test checker --quiet`, the conformance suite, Spoom, and
   Packwerk retain their classified results;
6. release-mode Rails measurements show no unexplained regression in discovery,
   registration, CFG construction, inference, or final reporting.
