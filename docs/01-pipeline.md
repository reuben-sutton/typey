# The checking pipeline

This chapter follows one invocation from the command line to the final
diagnostics. It is useful to keep open while reading `src/main.rs` and
`src/workspace.rs`.

## 1. Choosing an entry point

The command-line binary accepts a Ruby file, an RBI file, a directory, or
standard input. The directory form is the normal repository workflow:

    cargo build --release
    target/release/typey test_repos/spoom

`src/main.rs` is intentionally thin. It selects a path, enables debug output
when requested, and delegates the real work to the library API. The public
entry points are useful in tests and in future integrations:

- `check(source, config)` checks one source buffer.
- `check_with_policies(...)` checks source while applying typed-file and
  workspace policies.
- `check_workspace(paths, config)` loads a set of Ruby and RBI files and
  checks them together.

## 2. Discovering files

`src/workspace.rs` recursively discovers `.rb` and `.rbi` files. It sorts and
deduplicates paths, and skips generated or irrelevant trees such as `.git`,
`target`, `node_modules`, and upstream checkout directories.

The checker also loads the vendored Sorbet RBI collection under
`vendor/sorbet/rbi`. That collection is input, not application code. It gives
the checker contracts for Ruby and standard-library methods and should be
consulted before adding a handwritten built-in model.

## 3. Typed-file policy

Typey recognizes the first part of a file for a Sorbet `typed:` sigil. The
effective modes are:

| Mode | Meaning in Typey |
| --- | --- |
| `ignore` | Skip the file entirely. |
| `false` | Parse enough to retain syntax errors, but do not type-check it. |
| `true` | Check ordinary operations and report missing API use. |
| `strict` | Also require enough information to infer a complete method summary. |
| `strong` | The strongest mode when additional strictness rules apply. |

Files without a sigil default to `typed: true`. This makes an unannotated
repository measurable without pretending that every file has Sorbet's
strongest guarantees.

This policy is decided before ordinary analysis. It is not implemented by
turning all unknown expressions into `T.untyped`.

## 4. Parsing and annotation collection

Prism parses Ruby into an abstract syntax tree (AST). The AST gives Typey
source locations and Ruby structure: classes, method definitions, sends,
assignments, branches, blocks, rescue clauses, and so on.

Annotation collection is a separate pass. It finds:

- Sorbet `sig { ... }` blocks;
- RBS-style comments such as `#: (String) -> Integer`;
- type aliases;
- generic type parameters;
- attribute annotations;
- assertion declarations.

Keeping annotations separate from expression evaluation matters. A signature
before a method definition is a declaration about the method; it is not just
another expression to evaluate. Comments before `attr_reader` also need to be
attached to the generated reader rather than to the comment's line number.

## 5. Registering declarations

Before Typey can understand a call, it needs to know which methods and types
exist. Registration walks the AST and fills the analyzer's declaration tables.
Among other things it records:

- classes and modules;
- instance and singleton methods;
- visibility;
- inheritance, includes, prepends, and extensions;
- aliases;
- constants, class variables, globals, and ivars;
- accessors;
- type aliases and generic members;
- explicit signatures.

Methods are identified by a `MethodKey`:

    (owner, method name, singleton?)

    User#name      => (User, "name", false)
    User.find      => (User, "find", true)

The singleton bit is essential. `User.find` dispatches on the class object,
while `user.name` dispatches on an instance. Treating both as one method would
make constructors, class methods, and inherited singleton methods ambiguous.

Source declarations, project RBIs, and built-in RBIs are reconciled here.
An explicit source signature has the highest priority. A project RBI supplies
contracts for external or generated code. Built-in RBIs supply Ruby and
standard-library contracts. A declaration that exists but has no usable
signature must remain distinguishable from a declaration whose return type is
known to be `T.noreturn`.

## 6. The seed pass

The analyzer performs an initial evaluation pass without reporting ordinary
diagnostics. The purpose is to execute top-level code far enough to discover
which methods, shared state, and call relationships matter.

This pass seeds inferred method parameters and return summaries. For an
explicitly typed method, the signature is already a contract. For an
inferred method, the body supplies evidence:

    def label(user)
      user.name
    end

If `user.name` is known to return `String`, the call provides evidence for the
return summary of `label`. If the method is called with a known `User`, that
call also provides evidence for the parameter slot.

## 7. Fixpoint inference

Methods can depend on one another in cycles:

    def first(x)
      second(x)
    end

    def second(x)
      first(x)
    end

One evaluation is not enough to solve such a graph. Typey uses a worklist:

1. Schedule methods that need evaluation.
2. Evaluate them against the previous committed summaries.
3. Compare the candidate summary with the old summary.
4. Commit changes synchronously.
5. Schedule callers and readers affected by changed information.
6. Repeat until the worklist is empty.

Reading previous summaries during a pass and committing candidates afterward
prevents traversal order from deciding the answer. The implementation should
converge because type joins move toward a stable, less-specific upper bound.
There is no arbitrary “32 rounds means done” rule; if inference is slow, the
dependency graph or invalidation strategy should be investigated.

Dependencies include direct method calls and reads of shared declarations.
When a method summary changes, callers are scheduled. When a class, constant,
ivar, or other shared fact changes, readers are scheduled.

## 8. The final reporting pass

After summaries stabilize, Typey evaluates again with reporting enabled. This
pass emits diagnostics at their source spans and records inferred expression
types for metrics and tests.

Separating inference from reporting is important. A diagnostic encountered
while an early summary is still provisional should not be mistaken for a
final error. Conversely, the final pass must not silently skip a call just
because an earlier discovery pass saw it.

Workspace results map concatenated analysis ranges back to original paths.
Declarations from RBIs and built-ins can participate in inference without
their internal implementation details appearing as application diagnostics.

## 9. Debug output and performance

`--debug` prints phase progress and useful counts such as untyped origins,
application send coverage, strict-file coverage, and elapsed time. It is
observability, not profiling. A line saying that Typey is “registering
declarations” does not identify which operation consumed the time.

For performance work, measure release builds and separate discovery/loading,
registration, inference, and final reporting. Use an actual profiler or
instrumented timing around the suspected phase. A growing worklist may mean
that summaries are not converging, invalidation is too broad, or the same
method is repeatedly reevaluated without a changed input.
