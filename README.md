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

Run it on stdin or a file:

```text
cargo run -- path/to/file.rb
```

The checked-in fixtures under `tests/fixtures` use Sorbet's `# error:` style
expectations. They are a conformance seed, not the full Sorbet suite. A shallow
clone of Sorbet is kept locally as `sorbet-upstream/` for selecting and porting
fixtures; it is ignored by this crate so the large upstream checkout is not
vendored into Typey.

```text
cargo test
```
