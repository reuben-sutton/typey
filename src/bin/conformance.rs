use std::env;
use std::path::PathBuf;

use typey::conformance::{check_fixture, fixture_paths, manifest_paths};
use typey::CheckerConfig;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut root = None;
    let mut manifest = None;
    let mut arguments = env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--help" | "-h" => {
                println!(
                    "usage: conformance [FIXTURE_DIR_OR_FILE]\n       conformance --manifest MANIFEST"
                );
                return Ok(());
            }
            "--manifest" => {
                if manifest.is_some() {
                    return Err("--manifest may only be supplied once".into());
                }
                let path = arguments.next().ok_or("--manifest requires a path")?;
                manifest = Some(PathBuf::from(path));
            }
            _ if root.is_none() && manifest.is_none() => root = Some(PathBuf::from(argument)),
            _ => return Err(format!("unknown argument: {argument}").into()),
        }
    }

    let root = root.unwrap_or_else(|| PathBuf::from("tests/fixtures"));
    let requested = manifest.as_ref().map_or_else(
        || root.display().to_string(),
        |path| path.display().to_string(),
    );
    let paths = if let Some(manifest) = manifest {
        manifest_paths(&manifest)?
    } else {
        fixture_paths(&root)?
    };
    if paths.is_empty() {
        return Err(format!("no Ruby fixtures found below {requested}").into());
    }

    let mut passed = 0;
    let mut failed = 0;
    let mut expected_errors = 0;
    let mut expected_notes = 0;
    for path in paths {
        let report = check_fixture(&path, CheckerConfig::default())?;
        expected_errors += report
            .expected
            .iter()
            .filter(|expectation| expectation.severity == typey::diagnostic::Severity::Error)
            .count();
        expected_notes += report
            .expected
            .iter()
            .filter(|expectation| expectation.severity == typey::diagnostic::Severity::Note)
            .count();
        if report.passed() {
            passed += 1;
            println!("PASS {}", report.path.display());
        } else {
            failed += 1;
            println!("FAIL {}", report.path.display());
            for failure in &report.failures {
                println!("  {failure}");
            }
            for diagnostic in &report.result.diagnostics {
                println!("  {diagnostic}");
            }
        }
    }

    println!(
        "conformance: {} passed, {} failed; {} expected errors, {} expected notes",
        passed, failed, expected_errors, expected_notes
    );
    if failed == 0 {
        Ok(())
    } else {
        std::process::exit(1);
    }
}
