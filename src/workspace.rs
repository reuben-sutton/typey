//! Repository-oriented checking built on top of the single-buffer analyzer.
//!
//! A workspace is assembled into one Prism program after all Ruby source
//! files have been discovered. This lets the existing declaration registrar
//! and lattice fixpoint see methods, classes, RBI signatures, and call sites
//! across file boundaries without introducing a second parser or a Ruby
//! bridge. Diagnostics and inferred node types are mapped back to their
//! original files before they are returned.

use crate::diagnostic::{Diagnostic, Severity};
use crate::infer::{check_with_rbi_ranges, CheckerConfig};
use crate::types::Type;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

const SKIPPED_DIRECTORIES: &[&str] = &[
    ".git",
    "target",
    "node_modules",
    "sorbet-upstream",
    "spinel-upstream",
];

/// One Ruby source unit in a workspace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkspaceFile {
    pub path: PathBuf,
    pub source: String,
}

impl WorkspaceFile {
    #[must_use]
    pub fn new(path: impl Into<PathBuf>, source: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            source: source.into(),
        }
    }
}

/// A diagnostic associated with its original workspace file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkspaceDiagnostic {
    pub path: PathBuf,
    pub diagnostic: Diagnostic,
}

impl WorkspaceDiagnostic {
    #[must_use]
    pub fn render(&self) -> String {
        self.diagnostic.render(&self.path.display().to_string())
    }
}

/// A node type associated with its original workspace file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkspaceInferredType {
    pub path: PathBuf,
    pub start: usize,
    pub end: usize,
    pub type_: Type,
}

/// The result of checking all source units in a workspace.
#[derive(Clone, Debug, Default)]
pub struct WorkspaceCheckResult {
    pub diagnostics: Vec<WorkspaceDiagnostic>,
    pub types: Vec<WorkspaceInferredType>,
}

impl WorkspaceCheckResult {
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.diagnostic.severity == Severity::Error)
    }
}

/// Return whether a path is a Ruby implementation or RBI source file.
#[must_use]
pub fn is_ruby_source(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| matches!(extension, "rb" | "rbi"))
}

/// Discover `.rb` and `.rbi` files below a file or directory.
///
/// Results are sorted for deterministic analysis. Repository metadata and
/// generated/build directories are skipped, including the ignored upstream
/// checkouts used by this project for conformance work.
pub fn discover_ruby_files(root: &Path) -> io::Result<Vec<PathBuf>> {
    let metadata = fs::metadata(root)?;
    let mut paths = Vec::new();
    if metadata.is_file() {
        if is_ruby_source(root) {
            paths.push(root.to_owned());
        }
    } else if metadata.is_dir() {
        collect_ruby_files(root, &mut paths)?;
    }
    paths.sort();
    paths.dedup();
    Ok(paths)
}

/// Read all discovered Ruby and RBI files below `root`.
pub fn load_workspace(root: &Path) -> io::Result<Vec<WorkspaceFile>> {
    discover_ruby_files(root)?
        .into_iter()
        .map(|path| {
            let source = fs::read_to_string(&path)?;
            Ok(WorkspaceFile::new(path, source))
        })
        .collect()
}

/// Check multiple Ruby/RBI files as one shared inference workspace.
///
/// Declarations are registered across the assembled source before the
/// analyzer's normal fixpoint rounds run. The input order is retained, so
/// callers that need a load-order approximation can provide one explicitly;
/// [`discover_ruby_files`] supplies a deterministic lexical order.
#[must_use]
pub fn check_workspace(files: &[WorkspaceFile], config: CheckerConfig) -> WorkspaceCheckResult {
    if files.is_empty() {
        return WorkspaceCheckResult::default();
    }

    let mut combined = String::new();
    let mut ranges = Vec::with_capacity(files.len());
    let mut rbi_ranges = Vec::new();
    for file in files {
        let start = combined.len();
        combined.push_str(&file.source);
        let end = combined.len();
        ranges.push(SourceRange { start, end });
        if is_rbi_path(&file.path) {
            rbi_ranges.push((start, end));
        }

        // A non-comment boundary clears a pending `#:` signature from the
        // previous file. The expression is semantically inert and keeps the
        // source parseable while preserving line-based annotation behavior.
        combined.push_str("\n# typey workspace boundary\nnil\n\n");
    }

    let result = check_with_rbi_ranges(&combined, config, &rbi_ranges);
    let diagnostics = result
        .diagnostics
        .iter()
        .filter_map(|diagnostic| map_diagnostic(diagnostic, files, &ranges))
        .collect();
    let types = result
        .types
        .iter()
        .filter_map(|inferred| map_type(inferred, files, &ranges))
        .collect();

    WorkspaceCheckResult { diagnostics, types }
}

fn is_rbi_path(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension == "rbi")
}

#[derive(Clone, Copy, Debug)]
struct SourceRange {
    start: usize,
    end: usize,
}

fn map_diagnostic(
    diagnostic: &Diagnostic,
    files: &[WorkspaceFile],
    ranges: &[SourceRange],
) -> Option<WorkspaceDiagnostic> {
    let index = locate_offset(diagnostic.start, ranges)?;
    let range = ranges[index];
    let file = &files[index];
    let start = diagnostic
        .start
        .saturating_sub(range.start)
        .min(file.source.len());
    let end = diagnostic
        .end
        .saturating_sub(range.start)
        .min(file.source.len());
    Some(WorkspaceDiagnostic {
        path: file.path.clone(),
        diagnostic: Diagnostic::new(
            file.source.as_bytes(),
            diagnostic.severity,
            diagnostic.message.clone(),
            start,
            end.max(start),
        ),
    })
}

fn map_type(
    inferred: &crate::infer::InferredType,
    files: &[WorkspaceFile],
    ranges: &[SourceRange],
) -> Option<WorkspaceInferredType> {
    let index = ranges.iter().position(|range| {
        inferred.start >= range.start
            && inferred.start <= range.end
            && inferred.end >= inferred.start
            && inferred.end <= range.end
    })?;
    let range = ranges[index];
    let file = &files[index];
    Some(WorkspaceInferredType {
        path: file.path.clone(),
        start: inferred.start - range.start,
        end: inferred.end - range.start,
        type_: inferred.type_.clone(),
    })
}

fn locate_offset(offset: usize, ranges: &[SourceRange]) -> Option<usize> {
    ranges
        .iter()
        .position(|range| offset >= range.start && offset < range.end)
        .or_else(|| ranges.iter().position(|range| offset == range.end))
        .or_else(|| ranges.iter().position(|range| offset < range.start))
        .or_else(|| ranges.len().checked_sub(1))
}

fn collect_ruby_files(root: &Path, paths: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            let skipped = path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| SKIPPED_DIRECTORIES.contains(&name));
            if !skipped {
                collect_ruby_files(&path, paths)?;
            }
        } else if file_type.is_file() && is_ruby_source(&path) {
            paths.push(path);
        }
    }
    Ok(())
}
