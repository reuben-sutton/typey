//! Typey's public, hackable checker core.
//!
//! The library deliberately keeps parsing, annotations, the type lattice, and
//! inference in separate modules.  Embedders can use the lattice on its own or
//! call [`infer::check`] for a complete source-buffer check.

pub mod conformance;
pub mod diagnostic;
pub mod infer;
pub mod prism;
pub mod signature;
pub mod types;
pub mod workspace;

pub use infer::{check, CheckResult, CheckerConfig, InferredType, Strictness};
pub use types::{Type, TypeLattice};
pub use workspace::{
    check_workspace, discover_ruby_files, load_workspace, WorkspaceCheckResult,
    WorkspaceDiagnostic, WorkspaceFile, WorkspaceInferredType,
};
