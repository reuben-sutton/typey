use super::hash_shape::HashShape;
use super::MethodKey;
use crate::types::{Type, TypeLattice};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PredicateAlias {
    pub(super) source: String,
    pub(super) negated: bool,
    pub(super) expected: Option<Type>,
}

/// Abstract state for one Ruby evaluation context.
///
/// The environment is shared by the recursive evaluator and the owned CFG
/// transfer, but it contains no parser or CFG references. Keeping it here
/// makes path joins and refinements a transfer-layer concern rather than part
/// of the top-level inference host.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment {
    pub(super) locals: BTreeMap<String, Type>,
    /// Types learned from observed calls to an unsigiled method are useful
    /// for expression inference, but they are not a proof about every future
    /// call. Keep their provenance so control-flow predicates do not treat a
    /// sample argument as exhaustive.
    pub(super) inferred_locals: BTreeSet<String>,
    pub(super) provisional_locals: BTreeSet<String>,
    /// Locals introduced by a Ruby `&block` parameter.  A forwarded block
    /// needs a little more information than its ordinary `Proc` shape: the
    /// receiving method may pass it to another callback, where the expected
    /// parameters provide the missing signature.
    pub(super) block_parameters: BTreeSet<String>,
    pub(super) open_array_locals: BTreeSet<String>,
    pub(super) known_nonempty_arrays: BTreeSet<String>,
    pub(super) predicate_aliases: BTreeMap<String, PredicateAlias>,
    pub(super) known_truthiness: BTreeMap<String, bool>,
    /// Flow-local refinements for hashes whose literal keys are known. The
    /// ordinary local/ivar type remains an aggregate `Type::Hash`.
    pub(super) hash_shapes: BTreeMap<String, HashShape>,
    pub(super) self_type: Type,
    pub(super) method_key: Option<MethodKey>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            locals: BTreeMap::new(),
            inferred_locals: BTreeSet::new(),
            provisional_locals: BTreeSet::new(),
            block_parameters: BTreeSet::new(),
            open_array_locals: BTreeSet::new(),
            known_nonempty_arrays: BTreeSet::new(),
            predicate_aliases: BTreeMap::new(),
            known_truthiness: BTreeMap::new(),
            hash_shapes: BTreeMap::new(),
            self_type: Type::Object,
            method_key: None,
        }
    }
}

impl Environment {
    #[must_use]
    pub fn get(&self, name: &str) -> Type {
        self.locals.get(name).cloned().unwrap_or(Type::Any)
    }

    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.locals.contains_key(name)
    }

    pub fn bind(&mut self, name: impl Into<String>, type_: Type) {
        let name = name.into();
        self.open_array_locals.remove(&name);
        self.known_nonempty_arrays.remove(&name);
        self.inferred_locals.remove(&name);
        self.provisional_locals.remove(&name);
        self.block_parameters.remove(&name);
        self.locals.insert(name.clone(), type_);
        self.predicate_aliases.remove(&name);
        self.known_truthiness.remove(&name);
        self.hash_shapes.remove(&name);
        self.hash_shapes.remove(&format!("\u{1}local:{name}"));
    }

    pub(super) fn remove(&mut self, name: &str) {
        self.locals.remove(name);
        self.inferred_locals.remove(name);
        self.provisional_locals.remove(name);
        self.block_parameters.remove(name);
        self.open_array_locals.remove(name);
        self.known_nonempty_arrays.remove(name);
        self.predicate_aliases.remove(name);
        self.known_truthiness.remove(name);
        self.hash_shapes.remove(name);
        self.hash_shapes.remove(&format!("\u{1}local:{name}"));
    }

    pub(super) fn mark_inferred(&mut self, name: impl Into<String>) {
        let name = name.into();
        if self.locals.contains_key(&name) {
            self.provisional_locals.remove(&name);
            self.inferred_locals.insert(name);
        }
    }

    pub(super) fn mark_provisional(&mut self, name: impl Into<String>) {
        let name = name.into();
        if self.locals.contains_key(&name) {
            self.inferred_locals.remove(&name);
            self.provisional_locals.insert(name);
        }
    }

    pub(super) fn bind_block_parameter(&mut self, name: impl Into<String>, type_: Type) {
        let name = name.into();
        self.bind(name.clone(), type_);
        self.block_parameters.insert(name);
    }

    pub(super) fn is_block_parameter(&self, name: &str) -> bool {
        self.block_parameters.contains(name)
    }

    pub(super) fn is_inferred(&self, name: &str) -> bool {
        self.inferred_locals.contains(name)
    }

    pub(super) fn is_provisional(&self, name: &str) -> bool {
        self.provisional_locals.contains(name)
    }

    pub(super) fn bind_predicate_alias(
        &mut self,
        name: impl Into<String>,
        type_: Type,
        alias: PredicateAlias,
    ) {
        let name = name.into();
        self.open_array_locals.remove(&name);
        self.known_nonempty_arrays.remove(&name);
        self.inferred_locals.remove(&name);
        self.provisional_locals.remove(&name);
        self.locals.insert(name.clone(), type_);
        self.predicate_aliases.insert(name.clone(), alias);
        self.known_truthiness.remove(&name);
        self.hash_shapes.remove(&name);
        self.hash_shapes.remove(&format!("\u{1}local:{name}"));
    }

    pub(super) fn predicate_alias(&self, name: &str) -> Option<&PredicateAlias> {
        self.predicate_aliases.get(name)
    }

    pub(super) fn set_known_truthiness(&mut self, name: impl Into<String>, truthy: bool) {
        self.known_truthiness.insert(name.into(), truthy);
    }

    pub(super) fn known_truthiness(&self, name: &str) -> Option<bool> {
        self.known_truthiness.get(name).copied()
    }

    pub(super) fn hash_shape(&self, name: &str) -> Option<&HashShape> {
        self.hash_shapes.get(name)
    }

    pub(super) fn set_hash_shape(&mut self, name: impl Into<String>, shape: Option<HashShape>) {
        let name = name.into();
        if let Some(shape) = shape {
            self.hash_shapes.insert(name, shape);
        } else {
            self.hash_shapes.remove(&name);
        }
    }

    pub(super) fn set_known_nonempty_array(&mut self, name: impl Into<String>, nonempty: bool) {
        let name = name.into();
        if nonempty {
            self.known_nonempty_arrays.insert(name);
        } else {
            self.known_nonempty_arrays.remove(&name);
        }
    }

    pub(super) fn known_nonempty_array(&self, name: &str) -> bool {
        self.known_nonempty_arrays.contains(name)
    }

    /// Widen an array local whose empty literal was kept open for later
    /// appends. Empty arrays start with an `Any` element in the ordinary
    /// aggregate type, but that `Any` is only a placeholder until the first
    /// concrete write. Keep the open marker while updating the local so a
    /// chained or subsequent append continues to accumulate element types.
    pub(super) fn widen_open_array(&mut self, name: &str, arguments: &[Type]) -> Option<Type> {
        if !self.open_array_locals.contains(name) {
            return None;
        }
        let Type::Array(element) = self.locals.get(name)? else {
            return None;
        };
        let mut element = if element.is_any() {
            Type::Never
        } else {
            element.as_ref().clone()
        };
        for argument in arguments {
            element = element.join(argument);
        }
        let type_ = Type::Array(Box::new(element));
        self.locals.insert(name.to_owned(), type_.clone());
        Some(type_)
    }

    /// Join two control-flow environments using the same type lattice as
    /// expression inference. A local which exists on only one path can be
    /// `nil` when the other path is taken.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let lattice = TypeLattice;
        let mut result = Self {
            locals: BTreeMap::new(),
            inferred_locals: self
                .inferred_locals
                .union(&other.inferred_locals)
                .cloned()
                .collect(),
            provisional_locals: self
                .provisional_locals
                .union(&other.provisional_locals)
                .cloned()
                .collect(),
            block_parameters: self
                .block_parameters
                .intersection(&other.block_parameters)
                .cloned()
                .collect(),
            open_array_locals: self
                .open_array_locals
                .intersection(&other.open_array_locals)
                .cloned()
                .collect(),
            known_nonempty_arrays: self
                .known_nonempty_arrays
                .intersection(&other.known_nonempty_arrays)
                .cloned()
                .collect(),
            predicate_aliases: self
                .predicate_aliases
                .iter()
                .filter_map(|(name, alias)| {
                    (other.predicate_aliases.get(name) == Some(alias))
                        .then(|| (name.clone(), alias.clone()))
                })
                .collect(),
            known_truthiness: self
                .known_truthiness
                .iter()
                .filter_map(|(name, truthy)| {
                    (other.known_truthiness.get(name) == Some(truthy))
                        .then(|| (name.clone(), *truthy))
                })
                .collect(),
            hash_shapes: BTreeMap::new(),
            // `self` is flow-sensitive too: a predicate may narrow it on one
            // branch, and a join must retain the union of all feasible
            // receiver types rather than whichever branch happened to be
            // visited first.
            self_type: if self.self_type == other.self_type {
                self.self_type.clone()
            } else {
                lattice.join(&self.self_type, &other.self_type)
            },
            method_key: self.method_key.clone(),
        };
        for name in self.locals.keys().chain(other.locals.keys()) {
            if result.locals.contains_key(name) {
                continue;
            }
            let type_ = match (self.locals.get(name), other.locals.get(name)) {
                (Some(left), Some(right)) => lattice.join(left, right),
                (Some(value), None) | (None, Some(value)) => lattice.join(value, &Type::Nil),
                (None, None) => Type::Any,
            };
            result.locals.insert(name.clone(), type_);
        }
        for name in self.hash_shapes.keys().chain(other.hash_shapes.keys()) {
            if result.hash_shapes.contains_key(name) {
                continue;
            }
            let shape = match (self.hash_shapes.get(name), other.hash_shapes.get(name)) {
                (Some(left), Some(right)) => left.join(right),
                _ => continue,
            };
            result.hash_shapes.insert(name.clone(), shape);
        }
        result
    }

    #[must_use]
    pub fn narrowed(&self, name: &str, type_: Type) -> Self {
        let mut result = self.clone();
        result.bind(name.to_owned(), self.get(name).meet(&type_));
        result
    }
}
