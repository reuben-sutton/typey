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
  `T.assert_type!`, `T.reveal_type`, and `T.absurd`;
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
closure/yield propagation, refinements, and precise dynamic dispatch).

Run it on stdin or a file:

```text
cargo run -- path/to/file.rb
```

The checked-in fixtures under `tests/fixtures` use Sorbet's `# error:` and
`# note:` expectations. Run the reusable fixture harness with:

```text
cargo run --bin conformance
cargo run --bin conformance -- path/to/fixture-subset
cargo run --bin conformance -- path/to/one_fixture.rb
cargo run --bin conformance -- --manifest tests/upstream_manifest.txt
```

It recursively discovers `.rb` fixtures (or accepts one file), checks expected
error/note counts and message substrings, and reports suite coverage. A
manifest can select files from an external checkout such as `sorbet-upstream/`.
The checked-in set is a
conformance seed, not the full Sorbet suite. A shallow clone of Sorbet is kept
locally as `sorbet-upstream/` for selecting and porting fixtures; it is ignored
by this crate so the large upstream checkout is not vendored into Typey.

```text
cargo test
```
