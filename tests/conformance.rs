use std::path::Path;

use typey::conformance::{check_fixture, expectations, fixture_paths};
use typey::diagnostic::Severity;
use typey::CheckerConfig;

#[test]
fn all_checked_in_fixtures_match_inline_expectations() {
    let paths = fixture_paths(Path::new("tests/fixtures")).expect("fixture directory exists");
    assert!(
        !paths.is_empty(),
        "the conformance suite must contain fixtures"
    );

    let mut failures = Vec::new();
    for path in &paths {
        let report = check_fixture(path, CheckerConfig::default()).expect("fixture is readable");
        if !report.passed() {
            failures.push(format!("{}: {:?}", path.display(), report.failures));
        }
    }
    assert!(
        failures.is_empty(),
        "conformance failures:\n{}",
        failures.join("\n")
    );
}

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
    assert_eq!(parsed[1].severity, Severity::Note);
    assert_eq!(parsed[1].line, 2);
    assert_eq!(parsed[2].severity, Severity::Note);
    assert_eq!(parsed[2].message, "`Integer`");
    assert_eq!(parsed[3].severity, Severity::Note);
    assert_eq!(parsed[3].message, "a note");
    assert_eq!(parsed[4].severity, Severity::Error);
    assert_eq!(parsed[4].message, "caret-style expectation");
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
