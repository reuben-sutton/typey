//! Shared semantic keys used to connect inference services.
//!
//! These identifiers are deliberately independent of parser nodes. Keeping
//! them in one small module lets declaration registration, method lookup,
//! fixpoint scheduling, environments, and shared storage agree on identity
//! without making `infer.rs` own their representation.

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct MethodKey {
    pub(super) owner: Option<String>,
    pub(super) name: String,
    pub(super) singleton: bool,
}

impl MethodKey {
    pub(super) fn top_level(name: impl Into<String>) -> Self {
        Self {
            owner: None,
            name: name.into(),
            singleton: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct IvarKey {
    pub(super) owner: String,
    pub(super) singleton: bool,
    pub(super) name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ClassVarKey {
    pub(super) owner: String,
    pub(super) name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum SharedKey {
    Ivar(IvarKey),
    Constant(String),
    ClassVar(ClassVarKey),
    Global(String),
    StructField(String, String),
}

pub(super) fn ivar_refinement_key(name: &str) -> String {
    format!("\u{1}ivar:{name}")
}

pub(super) fn name_matches(name: &str, bare: &str) -> bool {
    name == bare || name == format!("T::{bare}")
}

pub(super) fn nominal_name(name: &str) -> &str {
    name.strip_prefix("T::").unwrap_or(name)
}
