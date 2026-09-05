use std::path::Path;

use typey::conformance::{check_fixture, fixture_paths};
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
