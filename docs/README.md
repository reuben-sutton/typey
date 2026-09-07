# Understanding Typey

Typey is a Ruby type checker written in Rust. It reads Ruby source files and
Ruby interface files (RBIs), builds one model of the program, infers types for
expressions and methods, and reports operations that are not safe according to
those types.

These docs are written for a reader who has never built a type checker. They
start with the overall execution pipeline and then explain the pieces that
make the pipeline precise: the type lattice, method inference, control-flow
facts, signatures, RBIs, tests, and extensions.

## Reading order

1. [The pipeline](01-pipeline.md) explains what happens during a check.
2. [Types and the lattice](02-types-and-lattice.md) explains what a type means
   internally and how types combine.
3. [Inference](03-inference.md) explains how expressions, calls, methods, and
   recursion are solved.
4. [Flow analysis](04-flow-analysis.md) explains why an `if value` branch can
   make a later expression safer.
5. [Signatures and RBIs](05-signatures-and-rbis.md) explains the contracts
   supplied by Sorbet syntax, RBS comments, and library declarations.
6. [Clean-room RBI, signature, and inference design](08-clean-room-rbi-signature-and-inference-design.md)
   specifies the declaration, annotation, registration, and fixpoint contracts
   for an independent implementation.
7. [Testing and debugging](06-testing-and-debugging.md) explains how to
   reproduce, classify, and verify behavior.
8. [Extending Typey](07-extending-typey.md) is a practical guide for adding
   precision without adding application-specific exceptions.

## The mental model

For a small Ruby program, imagine the checker doing this:

    Ruby/RBI files
          |
          v
    Prism syntax trees + type annotations
          |
          v
    Declaration tables
      (classes, methods, constants, ivars, signatures)
          |
          v
    Initial evaluation
      (discover dependencies and seed method summaries)
          |
          v
    Fixpoint worklist
      (re-evaluate methods whose inputs changed)
          |
          v
    Final checking pass
      (emit diagnostics and record inferred types)

The important word is **summary**. Typey does not need to re-run every method
forever. Each method gets a summary of the types it accepts and returns. When
one summary changes, only methods that depend on it need to be reconsidered.
The worklist stops when no summary changes.

## Three separate questions

When reading the code, keep these questions separate:

1. **What declarations exist?**
   Registration answers whether `User#name`, `User.find`, an ivar, or a
   constant is known.

2. **What type does this expression have?**
   Evaluation answers whether `user.name` is a `String`, `String | nil`, or
   something less precise.

3. **Is this operation allowed?**
   Checking answers whether a method exists for the receiver, arguments match
   the method contract, a value can be assigned, or a branch is unreachable.

Many apparent checker bugs are really failures in the first question. A
missing RBI method can make a valid call look invalid. Conversely, making
unknown things `T.untyped` can hide a real error in the third question.

## Typey's compatibility goal

Typey aims to behave observably like Sorbet where Sorbet's behavior is the
intended contract, while preserving concrete information whenever the source
and interfaces prove it. A lower diagnostic count is not automatically an
improvement:

- Sorbet may accept a call because a receiver is `T.untyped`.
- Typey may report a real application error that Sorbet does not reach.
- Typey may report a false positive because its model or flow analysis is
  incomplete.
- Typey may report fewer errors because a call site or dependency was never
  analyzed.

The right workflow is therefore: reproduce, classify, reduce to a fixture,
fix the general mechanism, and add a regression test.

## Current boundaries

Typey already models nominal classes, primitives, unions, intersections,
arrays, hashes, tuples, procs, generic parameters, blocks, inheritance,
modules, aliases, constructors, ivars, constants, class variables, globals,
many Ruby control-flow constructs, Sorbet's common `T.*` helpers, and a
vendored RBI collection.

Some Ruby and Sorbet features remain partial. When adding one, prefer a
general representation in the type, signature, evaluator, or flow layers.
Avoid changing application code merely to make a diagnostic disappear.
