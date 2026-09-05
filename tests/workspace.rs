use std::path::Path;
use std::process::Command;

use typey::{check_workspace, discover_ruby_files, load_workspace, CheckerConfig, WorkspaceFile};

const FIXTURE_ROOT: &str = "tests/workspace_repo";

#[test]
fn discovers_and_checks_rb_and_rbi_files_as_one_workspace() {
    let paths = discover_ruby_files(Path::new(FIXTURE_ROOT)).expect("workspace exists");
    assert_eq!(paths.len(), 3);
    assert!(paths
        .iter()
        .any(|path| path.extension().is_some_and(|ext| ext == "rb")));
    assert!(paths
        .iter()
        .any(|path| path.extension().is_some_and(|ext| ext == "rbi")));

    let files = load_workspace(Path::new(FIXTURE_ROOT)).expect("workspace loads");
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(
        !result.has_errors(),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.diagnostic.message.contains("Revealed type:"))
        .collect::<Vec<_>>();
    assert_eq!(notes.len(), 2, "{notes:?}");
    assert!(notes.iter().all(|diagnostic| diagnostic
        .path
        .ends_with("tests/workspace_repo/app/consumer.rb")));
    assert!(notes
        .iter()
        .all(|diagnostic| diagnostic.diagnostic.message.contains("`String`")));
}

#[test]
fn directory_cli_reports_original_file_paths() {
    let output = Command::new(env!("CARGO_BIN_EXE_typey"))
        .arg(FIXTURE_ROOT)
        .output()
        .expect("typey binary runs");
    assert!(
        output.status.success(),
        "status: {:?}\nstderr: {}\nstdout: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout
            .matches("tests/workspace_repo/app/consumer.rb")
            .count(),
        2,
        "{stdout}"
    );
    assert_eq!(
        stdout.matches("Revealed type: `String`").count(),
        2,
        "{stdout}"
    );
}

#[test]
fn direct_rbi_cli_accepts_declaration_stubs() {
    let output = Command::new(env!("CARGO_BIN_EXE_typey"))
        .arg("tests/workspace_repo/sorbet/rbi/greeting.rbi")
        .output()
        .expect("typey binary runs");
    assert!(
        output.status.success(),
        "status: {:?}\nstderr: {}\nstdout: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn debug_cli_reports_progress_on_stderr() {
    let output = Command::new(env!("CARGO_BIN_EXE_typey"))
        .args(["--debug", FIXTURE_ROOT])
        .output()
        .expect("typey binary runs");
    assert!(output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("discovering .rb/.rbi files"), "{stderr}");
    assert!(
        stderr.contains("registered 2 methods, 1 classes, and 0 type aliases"),
        "{stderr}"
    );
    assert!(stderr.contains("final reporting pass"), "{stderr}");
    assert!(
        output.stdout.is_ascii(),
        "stdout should contain diagnostics only"
    );
}

#[test]
fn workspace_skips_typed_ignore_files_before_combining_source() {
    let files = vec![
        WorkspaceFile::new(
            "ignored.rb",
            "# typed: ignore\ndef broken(\n  this is not valid Ruby\n",
        ),
        WorkspaceFile::new("valid.rb", "# typed: true\nvalue = 1\n"),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(
        result.diagnostics.is_empty(),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
}
