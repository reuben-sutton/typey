# Typey

Typey is a small, hackable Ruby type-checker core in Rust. Its inference state
is based on a structural type lattice: `T.noreturn` is bottom, `T.untyped` is
top, `join` is the least upper bound used at control-flow merges, and `meet` is
the greatest lower bound used for predicate refinement.

Ruby syntax is parsed directly with the [`ruby-prism`](https://crates.io/crates/ruby-prism)
crate. There is no Ruby process or bridge in the checker.

The first vertical slice supports:

- integer, float, string, symbol, boolean, nil, array, hash, proc, nominal,
  union, and intersection types;
- flow-sensitive local refinement for truthiness, `nil?`, and `is_a?`;
- a small, explicit Ruby core-method model;
- Sorbet `sig` blocks and `T.let`, `T.cast`, `T.must`, `T.unsafe`,
  `T.assert_type!`, `T.reveal_type`, `T.absurd`, `T.attached_class`, and
  method-level `T.type_parameter` substitution;
- inline RBS comments, always enabled, including `#:` method signatures,
  `#|` continuations, and trailing assertions.

Inference follows a small Spinel-style pipeline: method definitions are
registered before evaluation, call sites widen inferred parameter slots, and
method return summaries are refined through bounded lattice fixpoint rounds.
A final Prism traversal publishes diagnostics and per-node types. The current
flow engine also tracks owner-aware instance and singleton methods, simple
inheritance, constructor-to-`initialize` flow, instance variables, `case`,
`for`, loops, and locals captured by blocks.

This is still a conformance seed rather than a full Spinel or Sorbet
replacement. The current dispatch and flow slice also covers included and
prepended modules, method aliases, `super`, pattern captures, rescue/ensure,
lexical constants, class variables, globals, singleton classes, extension
modules, and basic `Proc` calls. Remaining gaps are richer destructuring and
exception edges, overloads and generic signatures, a complete Ruby
core/standard-library model, and the broader Spinel feature set (full
closure/yield propagation, refinements, generic class members, and precise
dynamic dispatch).

Run it on stdin, one file, or an entire repository:

```text
cargo run -- path/to/file.rb
cargo run -- path/to/repository
cargo run -- --debug path/to/repository
```

Directory mode recursively discovers `.rb` and `.rbi` files, registers their
classes, modules, method definitions, and signatures in one shared Prism
workspace, then runs the lattice fixpoint across the combined program. Output
diagnostics retain their source file paths. `.git`, `target`, `node_modules`,
and the ignored local `sorbet-upstream`/`spinel-upstream` checkouts are skipped.
Files with Sorbet's `# typed: ignore` sigil in their first twenty lines are
skipped before parsing and do not contribute declarations to the workspace.
Files are analyzed in deterministic lexical path order; library callers can
provide an explicit order with `check_workspace`.
Use `--debug` to print discovery, Prism, registration, fixpoint, and periodic
node-progress messages to stderr while keeping diagnostics on stdout.

The checked-in fixtures under `tests/fixtures` use Sorbet's `# error:` and
`# note:` expectations. Run the reusable fixture harness with:

```text
cargo run --bin conformance
cargo run --bin conformance -- path/to/fixture-subset
cargo run --bin conformance -- path/to/one_fixture.rb
cargo run --bin conformance -- --manifest tests/upstream_manifest.txt
```

It recursively discovers `.rb` and `.rbi` fixtures (or accepts one file),
checks expected error/note counts and message substrings, and reports suite
coverage. A manifest can select files from an external checkout such as
`sorbet-upstream/`.
The checked-in set is a conformance seed, not the full Sorbet suite. A shallow
clone of Sorbet is kept locally as `sorbet-upstream/` for selecting and porting
fixtures; it is ignored by this crate so the large upstream checkout is not
vendored into Typey.

```text
cargo test
```
