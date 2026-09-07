# HIR migration: steps 1 and 2

This is the implementation specification for the first two HIR steps:

1. introduce an owned, source-mapped semantic HIR;
2. lower calls and assignments into that HIR without changing inference
   behavior.

The purpose is to remove inference's direct dependence on Prism node lifetimes
and syntax-specific argument handling. This is an internal refactor. It must
not change diagnostics, inferred types, send metrics, or the treatment of
unknown values.

## Scope

These steps cover executable bodies, closures, calls, and assignments. The
existing declaration registrar remains authoritative for classes, methods,
signatures, ancestors, and RBIs. CFG construction, constraint solving, and
evidence tracking are explicitly later steps.

The HIR must not contain `Type`, `Environment`, `Diagnostic`, or framework
names. Rails and other library models consume HIR calls; they do not add
framework-specific HIR nodes.

## Step 1: owned semantic HIR

Add a `src/hir/` module with an owned representation. HIR values must not
store `ruby_prism::Node<'a>` references. Every node carries a file-relative
byte span:

```rust
struct Span {
    file: FileId,
    start: u32,
    end: u32,
}

struct Body {
    owner: BodyOwner,
    parameters: Parameters,
    root: ExprId,
}

struct Expr {
    span: Span,
    kind: ExprKind,
}
```

Use stable integer IDs backed by vectors (or an equivalent arena) for
expressions, bodies, and closures. IDs are internal to one lowered program and
must never be used as source locations.

The initial `ExprKind` set is:

```rust
enum ExprKind {
    Nil,
    Literal(Literal),
    Read(Read),
    Assign { target: AssignTarget, value: ExprId, operator: AssignOperator },
    Call(Call),
    Array(Vec<ArrayElement>),
    Hash(Vec<HashElement>),
    Closure(ClosureId),
    Sequence(Vec<ExprId>),
    If { condition: ExprId, then_body: ExprId, else_body: Option<ExprId> },
    Case(CaseExpr),
    Loop(LoopExpr),
    Begin(BeginExpr),
    Return(Option<ExprId>),
    Break(Option<ExprId>),
    Next(Option<ExprId>),
    Retry,
    Definition(DeclId),
}
```

Every Ruby construct remains value-producing. Control transfers are explicit
HIR nodes even though the later CFG pass will turn them into terminators.
This preserves Ruby's expression semantics and avoids prematurely pretending
that all statements are void.

Closures contain a body ID, parameters, and their source span. The HIR records
the closure's lexical scope, but does not decide what `self` will be when a
library method later executes it. That is an inference/modeling fact.

The lowerer must be total over the syntax accepted by the current checker. If
a construct is not yet lowered, represent it as an explicitly tagged
`Unsupported` node with its span and keep the existing Prism evaluator as a
temporary fallback. It must not silently disappear or become `T.untyped`.

## Step 2: lower calls and assignments

Calls must preserve Ruby's argument shape rather than becoming a flattened
list of inferred types:

```rust
struct Call {
    receiver: Receiver,
    name: Name,
    arguments: Vec<Argument>,
    block: Option<BlockArgument>,
    safe_navigation: bool,
    span: Span,
}

enum Receiver {
    Implicit,
    Explicit(ExprId),
    Super,
    Yield,
}

enum Argument {
    Positional(ExprId),
    Splat(ExprId),
    Keyword { name: Name, value: ExprId },
    KeywordSplat(ExprId),
    Forwarded,
}

enum BlockArgument {
    Inline(ClosureId),
    Passed(ExprId),
}
```

The following distinctions are mandatory:

* implicit, explicit, `super`, and `yield` receivers;
* safe-navigation calls;
* positional, splat, keyword, keyword-splat, and `...` forwarding arguments;
* inline blocks versus `&expression` block arguments, including `&nil`;
* exact call and block spans for diagnostics and send metrics.

Assignments use explicit targets and retain their operator:

```rust
enum AssignTarget {
    Local(LocalId),
    InstanceVariable(Name),
    ClassVariable(Name),
    Global(Name),
    Constant(ConstantPath),
    Attribute { receiver: ExprId, name: Name },
    Index { receiver: ExprId, arguments: Vec<Argument> },
}

enum AssignOperator {
    Set,
    And,
    Or,
    Binary(Name),
}
```

Do not desugar `&&=`, `||=`, indexed writes, or attribute writes into ordinary
method calls in this step. Their short-circuiting, read/write ordering, and
invalidation behavior are part of inference. A later CFG pass may lower them
to primitive operations while retaining the original span and target.

`CallArguments` may remain as an adapter during migration, but it must be
constructed from HIR rather than from Prism nodes. Once that adapter exists,
`eval_call` should consume the HIR `Call`; it must not re-inspect the Prism
`CallNode` to recover argument shape.

## Compatibility and tests

Add HIR lowering tests before switching inference:

* explicit and implicit calls;
* `super`, `yield`, safe navigation, and forwarding;
* positional/keyword/splat combinations;
* inline blocks, `&block`, and `&nil`;
* local, ivar, attribute, index, constant, compound, `&&=`, and `||=` writes;
* source spans for the call, receiver, arguments, block, and assignment target.

During the migration, each lowered fixture must be checked through both the
legacy and HIR paths and compared for:

* diagnostics and source locations;
* final inferred expression types and send flags;
* abrupt-flow outcomes;
* method-summary changes and fixpoint scheduling.

The existing conformance suite, checker suite, Spoom run, and Packwerk run are
the regression gates. A release-mode timing baseline must be recorded before
and after the switch; any material slowdown requires an explanation rather
than being hidden by a new fallback.

## Completion criteria

Steps 1 and 2 are complete when:

1. executable HIR is owned and source-mapped;
2. all call and assignment forms listed above lower without information loss;
3. `eval_call` and assignment evaluation use HIR data, not Prism nodes;
4. unsupported syntax is explicit and cannot silently produce `T.untyped`;
5. all existing tests and repository regression checks retain their classified
   behavior and diagnostic counts.
