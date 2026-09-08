use std::path::Path;

use typey::conformance::{check_fixture, expectations, fixture_paths};
use typey::diagnostic::Severity;
use typey::CheckerConfig;

fn assert_fixture_matches_expectations(path: &str) {
    let path = Path::new(path);
    let report = check_fixture(path, CheckerConfig::default()).expect("fixture is readable");
    assert!(report.passed(), "{}: {:?}", path.display(), report.failures);
}

macro_rules! conformance_fixture {
    ($name:ident, $path:literal) => {
        #[test]
        fn $name() {
            assert_fixture_matches_expectations($path);
        }
    };
}

include!(concat!(env!("OUT_DIR"), "/conformance_fixtures.rs"));

#[test]
fn parses_inline_expectations_with_reveal_compatibility() {
    let parsed = expectations(
        "value = 1 # error: Expected Integer\n\
         T.reveal_type(value) # error: Revealed type: `Integer`\n\
         T.reveal_type(value) # error: `Integer`\n\
         other = 2 # note: a note\n\
         #             ^ error: caret-style expectation\n\
         ignored = 3 # error:\n",
    );
    assert_eq!(parsed.len(), 5);
    assert_eq!(parsed[0].severity, Severity::Error);
    assert_eq!(parsed[0].line, 1);
    assert_eq!(parsed[0].message, "Expected Integer");
    assert_eq!(parsed[1].severity, Severity::Note);
    assert_eq!(parsed[1].line, 2);
    assert_eq!(parsed[1].message, "Revealed type: `Integer`");
    assert_eq!(parsed[2].severity, Severity::Note);
    assert_eq!(parsed[2].line, 3);
    assert_eq!(parsed[2].message, "`Integer`");
    assert_eq!(parsed[3].severity, Severity::Note);
    assert_eq!(parsed[3].line, 4);
    assert_eq!(parsed[3].message, "a note");
    assert_eq!(parsed[4].severity, Severity::Error);
    assert_eq!(parsed[4].line, 4);
    assert_eq!(parsed[4].message, "caret-style expectation");
}

#[test]
fn matches_expected_diagnostics_to_their_source_lines() {
    let path = Path::new("tests/fixtures/safe_navigation_narrowing.rb");
    let report = check_fixture(path, CheckerConfig::default()).expect("fixture is readable");

    assert!(report.passed(), "{:?}", report.failures);
    assert_eq!(report.expected.len(), 2);
    assert_eq!(report.result.diagnostics.len(), 2);
    for expectation in &report.expected {
        assert!(
            report.result.diagnostics.iter().any(|diagnostic| {
                diagnostic.line == expectation.line
                    && diagnostic.severity == expectation.severity
                    && diagnostic.message.contains(&expectation.message)
            }),
            "missing diagnostic for expectation {expectation:?}: {:?}",
            report.result.diagnostics
        );
    }
}

#[test]
fn maps_rbs_caret_expectations_to_the_following_definition() {
    let parsed = expectations(
        "#: (?Integer) -> void\n\
         #    ^^^^^^^ error: kind mismatch\n\
         def value(x); end\n",
    );
    assert_eq!(parsed.len(), 1);
    assert_eq!(parsed[0].line, 3);
    assert_eq!(parsed[0].message, "kind mismatch");
}

#[test]
fn maps_annotation_caret_expectations_to_the_following_definition() {
    let parsed = expectations(
        "# @interface\n\
         #  ^^^^^^^^^ error: interface mismatch\n\
         class Interface; end\n",
    );
    assert_eq!(parsed.len(), 1);
    assert_eq!(parsed[0].line, 3);
    assert_eq!(parsed[0].message, "interface mismatch");
}

#[test]
fn checks_rbi_fixtures_and_single_file_discovery() {
    let rbi = Path::new("tests/workspace_repo/sorbet/rbi/greeting.rbi");
    let report = check_fixture(rbi, CheckerConfig::default()).expect("RBI is readable");
    assert!(report.passed(), "{:?}", report.failures);
    assert!(report.expected.is_empty());

    assert_eq!(fixture_paths(rbi).unwrap(), vec![rbi.to_path_buf()]);
    assert!(fixture_paths(Path::new("Cargo.toml")).unwrap().is_empty());
}
