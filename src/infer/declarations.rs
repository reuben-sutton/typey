use super::{AccessorKind, ClassInfo, MethodKey, MethodState, ParameterShape};
use crate::types::Type;
use std::collections::{BTreeMap, HashSet};

/// Source and RBI declarations owned by the analyzer.
///
/// Keeping declaration storage together is important because method lookup,
/// generated accessors, aliases, constants, and nominal-name indexes are one
/// evolving graph. The evaluator may query this graph, but it should not need
/// to know which maps implement it.
#[derive(Default)]
pub(super) struct DeclarationState {
    pub(super) methods: BTreeMap<MethodKey, MethodState>,
    pub(super) definitions: BTreeMap<usize, MethodKey>,
    pub(super) parameter_shapes: BTreeMap<usize, ParameterShape>,
    pub(super) classes: BTreeMap<String, ClassInfo>,
    pub(super) class_name_set: HashSet<String>,
    pub(super) class_name_suffixes: BTreeMap<String, Vec<String>>,
    pub(super) aliases: BTreeMap<MethodKey, MethodKey>,
    pub(super) accessors: BTreeMap<MethodKey, AccessorKind>,
    pub(super) type_aliases: BTreeMap<String, Type>,
    pub(super) constants: BTreeMap<String, Type>,
    pub(super) constant_name_set: HashSet<String>,
    pub(super) constant_name_suffixes: BTreeMap<String, Vec<String>>,
    pub(super) struct_fields: BTreeMap<String, Vec<String>>,
    pub(super) struct_field_types: BTreeMap<(String, String), Type>,
}
