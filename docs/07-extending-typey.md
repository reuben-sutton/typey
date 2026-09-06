# Extending Typey safely

This is the practical chapter for someone about to change the checker. The
central rule is simple:

> Add the smallest general mechanism that explains a reduced fixture, then
> prove it with a regression test.

Typey is a compatibility project, so a clever local shortcut can easily make
one repository look better while making the checker less sound elsewhere.

## Choose the layer before writing code

Use the observed failure to select a layer:

| Failure | Likely layer |
| --- | --- |
| Ruby cannot be parsed | Prism integration or syntax traversal |
| Method/class/constant is missing | declaration registration or RBI loading |
| Wrong method implementation is selected | MethodKey or receiver dispatch |
| Signature is ignored or malformed | signature parser or annotation anchoring |
| Generic result is too broad | type-variable binding/substitution |
| Collection result loses its element type | structural type operation or builtin model |
| A branch does not narrow | predicate normalization or flow environment |
| Narrowing survives an assignment incorrectly | fact invalidation |
| Recursive inference is slow or unstable | dependency graph, summary equality, or worklist |
| Valid operation reports an error | one of the above, not application-code suppression |

Do not begin by editing the diagnostic message. The message is usually the
last symptom of a missing fact.

## The fixture-first loop

For a new feature or bug:

1. Write a tiny fixture that exposes the desired behavior.
2. Run the fixture and confirm the current failure.
3. Identify the missing fact by following the pipeline.
4. Implement the general rule.
5. Run the focused fixture.
6. Add nearby edge cases: unions, nil, unknown values, mutation, and abrupt
   flow where relevant.
7. Run the checker suite and formatting checks.
8. Run Spoom or another repository regression.
9. Measure diagnostic count and elapsed time.
10. Commit the logical change and its tests.

The fixture should use T.reveal_type when the result is about precision. A
diagnostic-only test cannot tell whether a call became quiet because its type
was inferred correctly or because it became T.untyped.

## Adding a Type variant

Most features do not need a new variant. Before adding one, check whether the
concept is:

- a union of existing alternatives;
- a flow fact that belongs in Environment;
- a receiver substitution such as attached class;
- a method contract represented by MethodSig;
- a structural container or Proc shape.

If a new variant is necessary, audit all type operations in src/types.rs:

1. display and parsing;
2. equality and normalization;
3. union/join;
4. meet;
5. without/removal;
6. subtype checking;
7. truthy and falsey parts;
8. generic substitution;
9. receiver ownership and method lookup;
10. diagnostics and test output.

Forgetting one operation often creates a bug that appears much later in
dispatch or flow analysis.

## Adding a built-in method model

Start with the RBI. Add a model only when a signature cannot express the
relationship or when the operation is central to inference.

For a collection method, decide:

- what receiver shapes are accepted;
- what arguments are required;
- what values the block receives;
- whether the block result becomes an element, key, value, or accumulator;
- whether the operation preserves or changes arity;
- how empty collections behave;
- how unknown and untyped inputs behave.

For example, map transforms an Array[T] into an Array[U] based on a block
returning U. Select keeps Array[T]. Reduce relates an accumulator to the
initial value and block result. To_h maps a pair-like element shape to a hash
key/value shape.

Add tests for concrete inputs and gradual inputs. A builtin model should not
invent a concrete result from an unknown receiver.

## Adding dispatch behavior

Dispatch is owner-aware. Keep these distinctions visible:

- instance method versus singleton method;
- class object versus instance;
- inherited method versus included/prepended method;
- alias versus an independently defined method;
- extension method versus ordinary class method;
- a union of receivers versus one broad owner.

When a method is missing, inspect the registered declarations and the candidate
search before adding a fallback. A fallback that returns T.untyped can hide
the missing registration bug and reduce application coverage.

## Adding signature support

Extend the signature representation before adding parser-only behavior. A
parameter feature may affect:

- argument arity;
- keyword handling;
- rest/splat checking;
- block checking;
- generic binding;
- inferred parameter slots;
- explicit-body checking.

For a new annotation syntax, add:

1. a parser fixture;
2. a source-location or attribute fixture if comments are involved;
3. a call-site check;
4. a body check;
5. a generic or nilable variant;
6. a conformance expectation when Sorbet/RBS behavior is the target.

Comments attached to generated methods must be anchored to the AST node that
owns the generated declaration, not simply to the preceding line.

## Adding flow facts

First decide whether the fact describes a value's type or an object's state.
Type narrowing is appropriate for predicates such as is_a? and nil?. Typestate
is appropriate for ActiveRecord persistence, ownership, lifecycle, or other
facts where the nominal class stays the same.

For a flow fact, define:

- its representation in Environment;
- how a predicate refines true and false paths;
- how assignment invalidates it;
- how a mutating call invalidates or transitions it;
- how branch and loop joins combine it;
- whether aliases may refer to it;
- whether it is valid after return, rescue, or ensure.

The join must be conservative. Retain a fact only if all normal incoming
paths establish it. This is the most important soundness rule in the flow
checker.

## Adding inference dependencies

If a method's answer depends on another method, register that dependency at
the call site. If it depends on a shared declaration such as an ivar type,
constant, class graph, or accessor, register a shared reader.

Then verify:

- the caller is rescheduled when the callee return changes;
- readers are rescheduled when the shared fact changes;
- summaries are compared structurally, not by unstable allocation identity;
- candidate updates are committed at a defined point;
- an unchanged summary does not trigger another round.

If the worklist grows unexpectedly, log the method key and the changed input.
Do not add a round cap as the first fix.

## Adding diagnostics and untyped accounting

Diagnostics should be emitted where the invalid operation occurs and should
retain the original source span. Keep notes and errors distinct.

When a result becomes untyped, record why. The origin may be explicit,
unsafe, declared, inferred, fallback, or propagated. This allows repository
metrics to distinguish intentional gradual typing from a missing checker
feature.

Never use untyped to silence:

- a missing RBI method;
- a wrong receiver owner;
- an unresolved generic that has concrete evidence;
- a flow fact that was accidentally dropped;
- a parser or AST traversal gap.

## Common anti-patterns

### Application-specific special cases

If one Rails model needs a rule, represent the general framework concept, such
as persisted typestate or schema nullability. Do not branch on the model's
name or edit its source to satisfy the checker.

### Syntax-only flow branches

Adding one more predicate spelling can patch a fixture while leaving aliases,
parentheses, conjunctions, mutation, or merges unsound. Normalize predicates
and use a reusable fact operation.

### Broad fallback return types

Returning T.untyped from every unsupported call reduces diagnostics but also
reduces measured typed coverage. First determine whether an RBI, dispatch rule,
generic substitution, or builtin model can provide a concrete type.

### Sorbet compatibility by deleting information

If Sorbet accepts a call because its receiver is untyped, Typey may still have
concrete evidence. Compatibility should preserve Sorbet's intentional gradual
boundary without throwing away independent proofs.

### Trusting progress output as profiling

A phase label identifies where the checker is, not why it is slow. Measure
phases and profile the hot path before changing worklist or registration logic.

## Review checklist

Before considering a change complete, ask:

- Is there a minimal fixture?
- Does the fixture reveal the concrete result, not merely absence of errors?
- Is the rule general rather than application-specific?
- Did the change preserve T.untyped, T.anything, and T.noreturn distinctions?
- Did it handle nilability, unions, and unknown inputs?
- Did it account for blocks, splats, generics, or attached types where relevant?
- Did it preserve flow through abrupt outcomes?
- Did it add or update dependencies for fixpoint inference?
- Did focused tests, the checker suite, formatting, and diff checks pass?
- Did Spoom remain correct, and did performance change?
- Is the commit narrow and free of temporary files?
