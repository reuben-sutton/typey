use crate::diagnostic::Severity;
use crate::infer::{check_with_rbi_ranges, InferredType};
use crate::workspace::is_ruby_source;
use crate::{
    builtin_rbi_paths, check, check_workspace, load_workspace_paths, CheckResult, CheckerConfig,
    WorkspaceFile,
};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// An inline expectation read from a fixture comment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InlineExpectation {
    pub severity: Severity,
    pub line: usize,
    pub message: String,
}

/// The result of checking one fixture against its inline expectations.
#[derive(Clone, Debug)]
pub struct FixtureReport {
    pub path: PathBuf,
    pub expected: Vec<InlineExpectation>,
    pub result: CheckResult,
    pub failures: Vec<String>,
}

impl FixtureReport {
    #[must_use]
    pub fn passed(&self) -> bool {
        self.failures.is_empty()
    }
}

/// Parse Sorbet-style diagnostic expectations from a source buffer.
#[must_use]
pub fn expectations(source: &str) -> Vec<InlineExpectation> {
    let mut result = Vec::new();
    for (index, line) in source.lines().enumerate() {
        for (severity, marker) in [(Severity::Error, "# error:"), (Severity::Note, "# note:")] {
            if let Some((prefix, message)) = line.split_once(marker) {
                let message = message.trim();
                if !message.is_empty() {
                    // Sorbet renders `T.reveal_type` as an error diagnostic in
                    // its test harness. Typey's public diagnostic model keeps
                    // reveals as notes, so accept either fixture spelling as
                    // the same semantic expectation.
                    let severity = if severity == Severity::Error
                        && (message.starts_with("Revealed type:")
                            || prefix.contains("T.reveal_type"))
                    {
                        Severity::Note
                    } else {
                        severity
                    };
                    result.push(InlineExpectation {
                        severity,
                        line: index + 1,
                        message: message.to_owned(),
                    });
                }
            }
        }
    }
    result
}

/// Read a manifest containing one Ruby fixture path per line. Blank lines and
/// lines beginning with `#` are ignored; relative paths are resolved from the
/// current working directory first and then from the manifest's directory.
pub fn manifest_paths(manifest: &Path) -> io::Result<Vec<PathBuf>> {
    let base = manifest.parent().unwrap_or_else(|| Path::new("."));
    let source = fs::read_to_string(manifest)?;
    let mut paths = Vec::new();
    for line in source.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let path = PathBuf::from(line);
        let path = if path.is_absolute() || path.exists() {
            path
        } else {
            base.join(path)
        };
        paths.push(path);
    }
    paths.sort();
    paths.dedup();
    Ok(paths)
}

/// Check a fixture file and compare its diagnostics with inline expectations.
pub fn check_fixture(path: &Path, config: CheckerConfig) -> io::Result<FixtureReport> {
    let source = fs::read_to_string(path)?;
    let expected = expectations(&source);
    let result = if path.extension().and_then(|extension| extension.to_str()) == Some("rbi") {
        check_with_rbi_ranges(&source, config, &[(0, source.len())])
    } else if let Ok(paths) = builtin_rbi_paths() {
        let mut files = load_workspace_paths(&paths)?;
        files.push(WorkspaceFile::new(path.to_owned(), source.clone()));
        let workspace = check_workspace(&files, config);
        CheckResult {
            diagnostics: workspace
                .diagnostics
                .into_iter()
                .filter(|diagnostic| diagnostic.path == path)
                .map(|diagnostic| diagnostic.diagnostic)
                .collect(),
            types: workspace
                .types
                .into_iter()
                .filter(|inferred| inferred.path == path)
                .map(|inferred| InferredType {
                    start: inferred.start,
                    end: inferred.end,
                    type_: inferred.type_,
                    untyped_origin: inferred.untyped_origin,
                    is_send: inferred.is_send,
                })
                .collect(),
        }
    } else {
        check(&source, config)
    };
    let mut failures = Vec::new();

    for severity in [Severity::Error, Severity::Note] {
        let expected_count = expected
            .iter()
            .filter(|expectation| expectation.severity == severity)
            .count();
        let actual_count = result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == severity)
            .count();
        if expected_count != actual_count {
            failures.push(format!(
                "expected {expected_count} {severity:?} diagnostics, found {actual_count}"
            ));
        }
    }

    let mut used = vec![false; result.diagnostics.len()];
    for expectation in &expected {
        let matching = result
            .diagnostics
            .iter()
            .enumerate()
            .find(|(index, diagnostic)| {
                !used[*index]
                    && diagnostic.severity == expectation.severity
                    && diagnostic.message.contains(&expectation.message)
            });
        if let Some((index, _)) = matching {
            used[index] = true;
        } else {
            failures.push(format!(
                "line {} did not produce {:?} containing `{}`",
                expectation.line, expectation.severity, expectation.message
            ));
        }
    }

    Ok(FixtureReport {
        path: path.to_owned(),
        expected,
        result,
        failures,
    })
}

/// Find Ruby fixtures recursively below `root` in stable path order.
pub fn fixture_paths(root: &Path) -> io::Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    if root.is_file() {
        if is_ruby_source(root) {
            paths.push(root.to_owned());
        }
    } else {
        collect_fixture_paths(root, &mut paths)?;
    }
    paths.sort();
    Ok(paths)
}

fn collect_fixture_paths(root: &Path, paths: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_fixture_paths(&path, paths)?;
        } else if file_type.is_file() && is_ruby_source(&path) {
            paths.push(path);
        }
    }
    Ok(())
}
