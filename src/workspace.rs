//! Repository-oriented checking built on top of the single-buffer analyzer.
//!
//! A workspace is assembled into one Prism program after all Ruby source
//! files have been discovered. This lets the existing declaration registrar
//! and lattice fixpoint see methods, classes, RBI signatures, and call sites
//! across file boundaries without introducing a second parser or a Ruby
//! bridge. Diagnostics and inferred node types are mapped back to their
//! original files before they are returned.

use crate::diagnostic::{Diagnostic, Severity};
use crate::directives::{effective_typed_mode, is_typed_ignore, typed_mode, TypedMode};
use crate::infer::{check_with_policies, CheckerConfig, Strictness, UntypedOrigin};
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
    pub untyped_origin: Option<UntypedOrigin>,
    pub is_send: bool,
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
    let ignores = sorbet_ignore_patterns(root)?;
    discover_ruby_files_with_ignores(root, &ignores)
}

fn discover_ruby_files_with_ignores(root: &Path, ignores: &[String]) -> io::Result<Vec<PathBuf>> {
    let metadata = fs::metadata(root)?;
    let mut paths = Vec::new();
    if metadata.is_file() {
        if is_ruby_source(root) {
            paths.push(root.to_owned());
        }
    } else if metadata.is_dir() {
        collect_ruby_files(root, root, ignores, &mut paths)?;
    }
    paths.sort();
    paths.dedup();
    Ok(paths)
}

/// Read all discovered Ruby and RBI files below `root`.
pub fn load_workspace(root: &Path) -> io::Result<Vec<WorkspaceFile>> {
    let paths = discover_ruby_files(root)?;
    load_workspace_paths(&paths)
}

/// Return the vendored Sorbet core and standard-library RBI files.
///
/// These declarations are the checker-wide Ruby baseline. Project-local RBIs
/// remain separate so callers can choose whether to load them, and can take
/// precedence when the same API is declared in both places.
pub fn builtin_rbi_paths() -> io::Result<Vec<PathBuf>> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("vendor/sorbet/rbi");
    discover_ruby_files_with_ignores(&root, &[])
}

/// Read a repository together with Typey's vendored Sorbet RBI baseline.
pub fn load_workspace_with_builtins(root: &Path) -> io::Result<Vec<WorkspaceFile>> {
    let mut paths = discover_ruby_files(root)?;
    paths.extend(builtin_rbi_paths()?);
    paths.sort();
    paths.dedup();
    load_workspace_paths(&paths)
}

/// Read an explicit, caller-provided workspace path order.
pub fn load_workspace_paths(paths: &[PathBuf]) -> io::Result<Vec<WorkspaceFile>> {
    paths
        .iter()
        .map(|path| {
            let source = fs::read_to_string(path)?;
            Ok(WorkspaceFile::new(path.clone(), source))
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
    let files = files
        .iter()
        .filter(|file| !is_typed_ignore(&file.source))
        .cloned()
        .collect::<Vec<_>>();
    if files.is_empty() {
        return WorkspaceCheckResult::default();
    }

    if config.debug {
        let rbi_count = files.iter().filter(|file| is_rbi_path(&file.path)).count();
        let bytes = files.iter().map(|file| file.source.len()).sum::<usize>();
        eprintln!(
            "[typey] workspace analysis: {} files ({} .rb, {} .rbi, {} bytes)",
            files.len(),
            files.len() - rbi_count,
            rbi_count,
            bytes
        );
        eprintln!("[typey] assembling workspace source");
    }

    let mut combined = String::new();
    let mut ranges = Vec::with_capacity(files.len());
    let mut rbi_ranges = Vec::new();
    let mut builtin_rbi_ranges = Vec::new();
    let mut strictness_ranges = Vec::new();
    for file in &files {
        let start = combined.len();
        combined.push_str(&file.source);
        let end = combined.len();
        ranges.push(SourceRange { start, end });
        let strictness = match effective_typed_mode(&file.source) {
            TypedMode::True => Some(Strictness::True),
            TypedMode::Strict => Some(Strictness::Strict),
            TypedMode::Strong => Some(Strictness::Strong),
            TypedMode::False | TypedMode::Ignore => None,
        };
        if let Some(strictness) = strictness {
            strictness_ranges.push((start, end, strictness));
        }
        if is_rbi_path(&file.path) {
            rbi_ranges.push((start, end));
            if is_builtin_rbi_path(&file.path) {
                builtin_rbi_ranges.push((start, end));
            }
        }

        // A non-comment boundary clears a pending `#:` signature from the
        // previous file. The expression is semantically inert and keeps the
        // source parseable while preserving line-based annotation behavior.
        combined.push_str("\n# typey workspace boundary\nnil\n\n");
    }

    if config.debug {
        eprintln!(
            "[typey] workspace source assembled: {} bytes",
            combined.len()
        );
    }
    let (result, parse_diagnostics) = check_with_policies(
        &combined,
        config,
        &rbi_ranges,
        &builtin_rbi_ranges,
        &strictness_ranges,
    );
    let diagnostics = result
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            let Some(index) = locate_offset(diagnostic.start, &ranges) else {
                return true;
            };
            let Some(file) = files.get(index) else {
                return true;
            };
            typed_mode(&file.source) != Some(TypedMode::False)
                || parse_diagnostics.contains(diagnostic)
        })
        .filter_map(|diagnostic| map_diagnostic(diagnostic, &files, &ranges))
        .collect();
    let types = result
        .types
        .iter()
        .filter_map(|inferred| map_type(inferred, &files, &ranges))
        .collect();

    WorkspaceCheckResult { diagnostics, types }
}

fn is_rbi_path(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension == "rbi")
}

fn is_builtin_rbi_path(path: &Path) -> bool {
    path.starts_with(Path::new(env!("CARGO_MANIFEST_DIR")).join("vendor/sorbet/rbi"))
        || path.starts_with(Path::new("vendor/sorbet/rbi"))
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
        untyped_origin: inferred.untyped_origin,
        is_send: inferred.is_send,
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

fn collect_ruby_files(
    root: &Path,
    base: &Path,
    ignores: &[String],
    paths: &mut Vec<PathBuf>,
) -> io::Result<()> {
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if is_ignored_path(base, &path, ignores) {
            continue;
        }
        if file_type.is_dir() {
            let skipped = path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| SKIPPED_DIRECTORIES.contains(&name));
            if !skipped {
                collect_ruby_files(&path, base, ignores, paths)?;
            }
        } else if file_type.is_file() && is_ruby_source(&path) {
            paths.push(path);
        }
    }
    Ok(())
}

fn sorbet_ignore_patterns(root: &Path) -> io::Result<Vec<String>> {
    let config = if root.is_dir() {
        root.join("sorbet/config")
    } else {
        return Ok(Vec::new());
    };
    if !config.is_file() {
        return Ok(Vec::new());
    }

    let contents = fs::read_to_string(config)?;
    let mut ignores = Vec::new();
    let mut expecting_value = false;
    for line in contents.lines() {
        let option = line.trim();
        if expecting_value {
            if !option.is_empty() && !option.starts_with('#') {
                ignores.push(option.to_owned());
                expecting_value = false;
            }
            continue;
        }
        if let Some(pattern) = option.strip_prefix("--ignore=") {
            if !pattern.is_empty() {
                ignores.push(pattern.to_owned());
            }
        } else if option == "--ignore" {
            expecting_value = true;
        }
    }
    Ok(ignores)
}

fn is_ignored_path(base: &Path, path: &Path, ignores: &[String]) -> bool {
    let Ok(relative) = path.strip_prefix(base) else {
        return false;
    };
    let components = relative
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>();
    let relative = components.join("/");
    ignores.iter().any(|pattern| {
        let anchored = pattern.starts_with('/');
        let pattern = pattern.trim_matches('/');
        if pattern.is_empty() {
            return false;
        }
        let pattern_components = pattern.split('/').collect::<Vec<_>>();
        if pattern_components.len() == 1 {
            if anchored {
                return components.first().copied() == Some(pattern);
            }
            return components.iter().any(|component| *component == pattern);
        }
        if anchored {
            relative == pattern || relative.starts_with(&format!("{pattern}/"))
        } else {
            components
                .windows(pattern_components.len())
                .any(|window| window == pattern_components.as_slice())
        }
    })
}
