use std::path::Path;

use typey::conformance::{check_fixture, manifest_paths};
use typey::CheckerConfig;

#[test]
fn selected_upstream_fixtures_match_when_checkout_is_available() {
    let paths = manifest_paths(Path::new("tests/upstream_manifest.txt"))
        .expect("upstream manifest is readable");
    assert_eq!(paths.len(), 39, "the selected upstream smoke suite changed");

    let mut checked = 0;
    let mut failures = Vec::new();
    for path in paths {
        if !path.is_file() {
            eprintln!("SKIP {} (upstream checkout is unavailable)", path.display());
            continue;
        }
        checked += 1;
        let report = check_fixture(&path, CheckerConfig::default()).expect("fixture is readable");
        if !report.passed() {
            failures.push(format!("{}: {:?}", path.display(), report.failures));
        }
    }

    if checked == 0 {
        eprintln!("SKIP upstream smoke suite: no listed fixture is available");
    }
    assert!(
        failures.is_empty(),
        "upstream conformance failures:\n{}",
        failures.join("\n")
    );
}
