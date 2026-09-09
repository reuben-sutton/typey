//! Flow-local facts for hash literals.
//!
//! `Type::Hash` deliberately describes an aggregate key/value contract.  A
//! CFG transfer can nevertheless know more about a literal hash, such as the
//! type of the value stored under one symbol key.  Keep that refinement out
//! of the public type lattice and carry it as abstract-state metadata.

use crate::cfg;
use crate::hir::{self, ExprKind, HashElement, Literal};
use crate::types::Type;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum HashKey {
    String(String),
    Symbol(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct HashShape {
    pub(super) entries: BTreeMap<HashKey, Type>,
    /// Values that may be present under a key not represented in `entries`.
    pub(super) unknown_value: Option<Type>,
}

impl HashShape {
    pub(super) fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
            unknown_value: None,
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        let mut entries = BTreeMap::new();
        for key in self.entries.keys().chain(other.entries.keys()) {
            if entries.contains_key(key) {
                continue;
            }
            let type_ = match (self.entries.get(key), other.entries.get(key)) {
                (Some(left), Some(right)) => left.join(right),
                (Some(value), None) | (None, Some(value)) => value.join(&Type::Nil),
                (None, None) => Type::Nil,
            };
            entries.insert(key.clone(), type_);
        }
        let unknown_value = match (&self.unknown_value, &other.unknown_value) {
            (Some(left), Some(right)) => Some(left.join(right)),
            (Some(value), None) | (None, Some(value)) => Some(value.join(&Type::Nil)),
            (None, None) => None,
        };
        Self {
            entries,
            unknown_value,
        }
    }

    pub(super) fn value_for(&self, key: &HashKey) -> Type {
        let known = self.entries.get(key).cloned();
        let unknown = self.unknown_value.clone();
        match (known, unknown) {
            (Some(known), Some(unknown)) => known.join(&unknown),
            (Some(known), None) => known,
            (None, Some(unknown)) => Type::union([Type::Nil, unknown]),
            (None, None) => Type::Nil,
        }
    }

    fn insert(&mut self, key: HashKey, value: Type) {
        self.entries.insert(key, value);
    }

    pub(super) fn write(&mut self, key: HashKey, value: Type) {
        self.insert(key, value);
    }

    fn merge(&mut self, other: &Self) {
        for (key, value) in &other.entries {
            self.insert(key.clone(), value.clone());
        }
        if let Some(value) = &other.unknown_value {
            self.unknown_value = Some(match self.unknown_value.take() {
                Some(current) => current.join(value),
                None => value.clone(),
            });
        }
    }
}

pub(super) fn from_cfg_hash(
    program: &hir::Program,
    expression: Option<hir::ExprId>,
    elements: &[cfg::HashOperand],
    values: &[Option<Type>],
    shapes: &[Option<HashShape>],
) -> Option<HashShape> {
    let expression = expression.and_then(|id| program.expression(id))?;
    let ExprKind::Hash(hir_elements) = &expression.kind else {
        return None;
    };
    if hir_elements.len() != elements.len() {
        return None;
    }

    let mut shape = HashShape::new();
    for (hir_element, cfg_element) in hir_elements.iter().zip(elements) {
        match (hir_element, cfg_element) {
            (
                HashElement::Pair { key, value: _ },
                cfg::HashOperand::Pair {
                    key: key_id,
                    value: value_id,
                },
            ) => {
                let value = values.get(value_id.0 as usize).cloned().flatten()?;
                if let Some(key) = literal_key(program, *key) {
                    shape.insert(key, value);
                } else {
                    shape.unknown_value = Some(match shape.unknown_value.take() {
                        Some(current) => current.join(&value),
                        None => value,
                    });
                }
                // Keep this operand in the contract even though its type is
                // already represented by the HIR pair. It prevents a future
                // lowering change from silently accepting misaligned data.
                if values.get(key_id.0 as usize).is_none() {
                    return None;
                }
            }
            (HashElement::Splat { value: _, .. }, cfg::HashOperand::Splat { value, .. }) => {
                let splat_type = values.get(value.0 as usize).cloned().flatten()?;
                if let Some(splat_shape) = shapes.get(value.0 as usize).cloned().flatten() {
                    shape.merge(&splat_shape);
                } else {
                    let value = match splat_type {
                        Type::Hash(_, value) => *value,
                        Type::Any => Type::Any,
                        _ => Type::Any,
                    };
                    shape.unknown_value = Some(match shape.unknown_value.take() {
                        Some(current) => current.join(&value),
                        None => value,
                    });
                }
            }
            _ => return None,
        }
    }
    Some(shape)
}

pub(super) fn literal_key(program: &hir::Program, expression: hir::ExprId) -> Option<HashKey> {
    let expression = program.expression(expression)?;
    match &expression.kind {
        ExprKind::Literal(Literal::Symbol(name)) => Some(HashKey::Symbol(name.clone())),
        ExprKind::Literal(Literal::String(value)) => Some(HashKey::String(value.clone())),
        _ => None,
    }
}
