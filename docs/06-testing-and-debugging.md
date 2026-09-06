# Testing and debugging

Type-checker work is unusually vulnerable to plausible but wrong fixes. A
diagnostic count can improve because a real error disappeared, because a
missing call was never visited, or because everything became untyped. Tests
must therefore verify both the reported errors and the inferred types.

## The baseline loop

Start every investigation with repository state:

    git status --short
    git log -1 --oneline

Then reproduce with a release build:

    cargo build --release
    target/release/typey test_repos/spoom

Use debug output for phase counts:

    target/release/typey --debug test_repos/spoom

After a code change, run focused tests first:

    cargo test --test checker --quiet
    cargo fmt -- --check
    git diff --check

Changes to shared type, parser, workspace, or fixpoint logic deserve the full
test suite and a fresh release-binary repository run.

## Fixture-first development

Reduce a bug to the smallest Ruby program that still demonstrates it. A good
fixture makes the intended type visible:

    # typed: true
    class Box
      def initialize(value)
        @value = value
      end

      def value
        @value
      end
    end

    value = Box.new("ok").value
    T.reveal_type(value) # should reveal String

A fixture should answer one question. Separate dispatch, flow, generic,
signature, and parser behavior when possible. Small fixtures are easier to
reason about than a full Rails application and make regressions permanent.

The fixture harness is in src/conformance.rs. Inline expectations use comments
such as:

    # error: Expected String, got Integer
    # note: Revealed type: String

The exact expectation syntax in an existing fixture is the source of truth;
copy its style when adding a case.

## What to assert

A strong regression test can check several layers:

- the expected diagnostic appears at the correct source span;
- a valid operation does not produce a diagnostic;
- T.reveal_type reports the intended concrete type;
- nilability is retained or removed only on the intended path;
- an explicit signature is not widened;
- a generic variable is substituted;
- a block receives the correct yield type;
- a splat preserves known arity;
- an untyped origin is the intended category;
- strict mode reports incomplete summaries when it should.

If a change only makes a large repository quieter, add a fixture before
trusting it.

## Comparing Typey and Sorbet

When compatibility matters, run both checkers on the same repository. For
Spoom, Sorbet can be invoked from its checkout with the configured Ruby:

    cd test_repos/spoom
    PATH=/opt/homebrew/opt/ruby/bin:$PATH bundle exec srb tc

Then run Typey from the Typey root:

    target/release/typey test_repos/spoom

Do not compare only total counts. Build a list of corresponding source spans
and classify differences:

1. true program error;
2. Typey inference or control-flow bug;
3. missing or incorrect library/RBI model;
4. unsupported Sorbet/Ruby feature;
5. intentional gradual-typing behavior;
6. unvisited call or incomplete coverage;
7. performance or convergence failure.

Sorbet can accept a call because a receiver is T.untyped. That is evidence
about gradual behavior, not proof that Typey's concrete diagnostic is wrong.
Conversely, Typey can report fewer diagnostics because a call was not modeled
or not scheduled. Fewer is not automatically better.

## Spoom, Packwerk, and Rails

Spoom is the primary application regression check. It is small enough to run
frequently and contains useful Ruby and Sorbet patterns:

    target/release/typey test_repos/spoom

Packwerk is another compatibility sample:

    target/release/typey test_repos/packwerk

Rails is large. Analyze one component while debugging:

    target/release/typey test_repos/rails/activesupport/lib

Record diagnostic count, representative messages, and elapsed time. If a
change is intended to alter behavior, explain which findings were reclassified
and why.

## Interpreting Typey's metrics

Typey reports application send coverage in debug mode. The useful distinction
is:

- sends with a concrete recorded type;
- sends recorded as untyped;
- sends that were not recorded at all.

An untyped send can be intentional or propagated from a boundary. An
unrecorded send is more suspicious: it may indicate a skipped file, an AST
path not visited, a missing final reporting pass, or a method that was never
scheduled. Always investigate the unrecorded category separately.

Similarly, strict inferred-type diagnostics mean that a method summary lacks
enough information for strict mode. They do not necessarily mean the program
has a bad runtime operation.

## Debug output is not a profiler

Progress lines such as “registering declarations” or “fixpoint round 1”
describe phase boundaries and counts. They do not say where CPU time or stack
depth is going.

For performance:

1. build in release mode;
2. measure discovery/loading, registration, inference, and reporting
   separately;
3. use a profiler or instrumented build;
4. inspect worklist size and repeated method evaluation;
5. check whether dependency invalidation is too broad;
6. compare before and after on the same checkout.

An arbitrary round limit hides convergence bugs. If a run grows from tens of
thousands to hundreds of thousands of visited nodes, determine which summary
or dependency keeps changing.

## Safe commits

Commit after each logical fix or tightly coupled test/model step:

    git add path/to/intended/files
    git commit -m "Describe the narrow behavior change"

Stage explicit paths. Preserve unrelated modifications and untracked debug
files. A clean, narrow commit makes it possible to compare diagnostic counts,
revert one inference idea, and identify which change affected performance.
