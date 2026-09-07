//! Typey's public, hackable checker core.
//!
//! The library deliberately keeps parsing, annotations, the type lattice, and
//! inference in separate modules.  Embedders can use the lattice on its own or
//! call [`infer::check`] for a complete source-buffer check.

pub mod conformance;
pub mod diagnostic;
pub mod directives;
pub mod hir;
pub mod infer;
pub mod prism;
pub mod signature;
pub mod types;
pub mod workspace;

pub use infer::{check, CheckResult, CheckerConfig, InferredType, Strictness, UntypedOrigin};
pub use types::{Type, TypeLattice};
pub use workspace::{
    builtin_rbi_paths, check_workspace, discover_ruby_files, discover_ruby_files_with_ignores,
    load_workspace, load_workspace_paths, load_workspace_with_builtins, WorkspaceCheckResult,
    WorkspaceDiagnostic, WorkspaceFile, WorkspaceInferredType,
};
