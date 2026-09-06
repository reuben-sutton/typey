# AGENTS.md

## Project purpose

Typey is a Rust implementation of a Sorbet-compatible Ruby type checker. It
uses Prism to parse Ruby, registers source and RBI declarations into one
workspace, and infers types through a lattice and fixpoint rounds.

The compatibility target is Sorbet's observable behavior, but Typey should
retain concrete information whenever it can prove it. The goal is not to make
the checker quiet by replacing uncertainty with `T.untyped`.

## Standard workflow for compatibility work

1. Start with a clean read of the working tree:

   ```text
   git status --short
   git log -1 --oneline
   ```

   Preserve existing user changes and unrelated untracked files. Do not reset,
   discard, or stage them accidentally.

2. Reproduce the diagnostic with the release binary when measuring a repository:

   ```text
   cargo build --release
   target/release/typey test_repos/spoom
   ```

   Use `--debug` for phase and progress messages. Progress output is not a
   profiler; use an actual profiler or a separately measured instrumented build
   when investigating performance.

3. Inspect the reported source, its declared signature, the relevant RBI, and
   the inferred receiver and argument types. Compare with Sorbet where useful.
   Do not assume that a difference from Sorbet is automatically a Typey bug:
   Sorbet may be accepting an operation through `T.untyped`.

4. Classify the finding before changing code:

   - true program error;
   - Typey inference or control-flow bug;
   - missing or incorrect library/RBI model;
   - unsupported Sorbet/Ruby feature;
   - intentional gradual-typing behavior;
   - performance or convergence problem.

5. Reduce each checker bug to a small fixture. Implement the most general
   checker or library-model fix that explains the fixture. Do not edit
   application code merely to silence Typey, and do not add application-specific
   special cases when a reusable rule is possible.

6. Add regression coverage before moving on. Use a fixture under
   `tests/fixtures/` for user-visible inference or diagnostic behavior and add
   the corresponding assertion in `tests/checker.rs` when the case needs more
   than the conformance harness. Add a conformance expectation when matching
   Sorbet behavior is the point of the test.

7. Run focused tests, then the checker suite:

   ```text
   cargo test --test checker --quiet
   cargo fmt -- --check
   git diff --check
   ```

   Run the full test suite for changes to shared type, parser, workspace, or
   fixpoint logic. Rerun the affected repository after rebuilding release mode
   and record diagnostic counts, representative messages, and elapsed time.

8. Commit after every logical fix or tightly coupled test/model step. Keep
   commits narrow and descriptive. Stage only intended files; never include
   temporary debugging files or unrelated working-tree changes.

## Diagnostic adjudication

When Typey reports more diagnostics than Sorbet, check whether Sorbet's result
is caused by an untyped receiver, missing declaration, or a deliberately
gradual operation. When Typey reports fewer, investigate missing call sites,
unmodeled methods, overly broad fallback types, and accidental propagation of
`T.untyped`.

A diagnostic is a false positive only when the operation is valid under the
available concrete program and library information. A missing method or
signature is normally a modeling gap, not a reason to weaken checking globally.

## Type and inference principles

- Never return `T.untyped` when a concrete type is provable from the receiver,
  arguments, signature, control-flow path, or an RBI.
- Do not invent a concrete type when the available information is genuinely
  unknown. Preserve the distinction between `T.untyped`, `T.anything`, and
  `T.noreturn`.
- Resolve generic parameters and container members through the actual receiver
  type. Do not allow unresolved type variables such as `U` or `V` to leak into
  user-facing inferred types; use gradual fallback only when inference truly
  has no evidence.
- Preserve Sorbet features rather than special-casing them away, including
  splats, optional blocks, `T.cast`, `T.must`, `T.unsafe`, `T.attached_class`,
  `T.self_type`, type parameters, overloads, and block signatures.
- Use the vendored Sorbet RBI collection as the baseline for Ruby and standard
  library behavior. Project RBIs are input used to obtain gem and application
  types; they should not be rewritten just to make Typey agree. Improve
  Typey's own models or add a narrowly scoped RBI only when that is the actual
  missing contract.

## Flow-sensitive analysis

Flow refinements must be path-sensitive and must join conservatively. A
refinement should be retained after a merge only when it holds on every normal
path. Reassignment and known mutating operations must invalidate facts when
necessary.

Prefer general flow facts over adding another syntax-only branch to the
predicate checker. Type narrowing and object-state facts are different things:
an object such as an ActiveRecord model can be the same nominal class while
being persisted, new, or destroyed. A framework rule such as `persisted?`
should therefore refine a tracked state fact, not globally change the class's
type or strip nilability from every method. Persistence also does not prove a
nullable database column is non-nil; only schema or generated persisted-field
metadata can establish that.

## Repository regression checks

Spoom is the primary application regression check:

```text
target/release/typey test_repos/spoom
```

Sorbet's baseline can be run from that repository with the configured Homebrew
Ruby, for example:

```text
cd test_repos/spoom
PATH=/opt/homebrew/opt/ruby/bin:$PATH bundle exec srb tc
```

Packwerk is another useful compatibility check. Rails is large and expensive;
analyze one component at a time, such as
`test_repos/rails/activesupport/lib`, rather than repeatedly running the whole
repository while debugging a local issue.

Track whether a change improves or worsens both correctness and performance.
Do not treat a lower diagnostic count as progress until the removed findings
have been classified.

## Performance and convergence

Measure release builds and separate discovery/loading, declaration
registration, fixpoint inference, and final diagnostic traversal. If a round
visits unexpectedly many nodes, determine whether methods are being repeatedly
reevaluated, whether dependencies are scheduling too broadly, or whether a
summary is failing to converge. Prefer memoized summaries and precise
invalidation to arbitrary round limits or broad suppression.

