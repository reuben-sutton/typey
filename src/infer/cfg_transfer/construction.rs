//! Owned CFG transfer for array and hash construction.

use super::super::{Analyzer, Environment, SourceSite};
use crate::cfg;
use crate::types::Type;

pub(super) fn transfer_array<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    elements: &[cfg::ArrayOperand],
    values: &[Option<Type>],
    preserve_fixed_shape: bool,
    defer_inline_assertion: bool,
    environment: &mut Environment,
) -> Option<Type> {
    let mut element_types = Vec::with_capacity(elements.len());
    let mut fixed_length = true;
    let mut element = Type::Never;
    for operand in elements {
        let (value, splat_span) = match operand {
            cfg::ArrayOperand::Value(value) => (value, None),
            cfg::ArrayOperand::Splat { value, span } => (value, Some(*span)),
        };
        let type_ = values.get(value.0 as usize).cloned().flatten()?;
        let type_ = if let Some(span) = splat_span {
            fixed_length = false;
            let element_type = analyzer.array_element_type(&type_);
            analyzer.record_at(
                SourceSite::from_span(span, None),
                type_.clone(),
                false,
                None,
            );
            element_type
        } else {
            type_
        };
        element_types.push(type_.clone());
        element = element.join(&type_);
    }
    let element = if element.is_never() {
        if analyzer.preserve_literal_tuples {
            Type::Never
        } else {
            Type::Any
        }
    } else {
        element
    };
    let inferred = if fixed_length
        && (preserve_fixed_shape
            || (analyzer.preserve_literal_tuples && analyzer.literal_tuple_depth == 0)
            || analyzer.expected_return_type.as_ref().is_some_and(|expected| {
                matches!(expected, Type::Tuple(expected) if expected.len() == element_types.len())
            }))
    {
        Type::Tuple(element_types)
    } else {
        Type::Array(Box::new(element))
    };
    Some(if defer_inline_assertion {
        inferred
    } else {
        analyzer.apply_inline_assertion_in_environment_at(site, inferred, environment)
    })
}

pub(super) fn transfer_hash<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    elements: &[cfg::HashOperand],
    values: &[Option<Type>],
    defer_inline_assertion: bool,
    environment: &mut Environment,
) -> Option<Type> {
    let mut key = Type::Never;
    let mut value = Type::Never;
    for element in elements {
        match element {
            cfg::HashOperand::Pair {
                key: key_id,
                value: value_id,
            } => {
                key = key.join(&values.get(key_id.0 as usize).cloned().flatten()?);
                value = value.join(&values.get(value_id.0 as usize).cloned().flatten()?);
            }
            cfg::HashOperand::Splat {
                value: value_id, ..
            } => match values.get(value_id.0 as usize).cloned().flatten()? {
                Type::Hash(splat_key, splat_value) => {
                    key = key.join(&splat_key);
                    value = value.join(&splat_value);
                }
                Type::Any => {
                    key = Type::Any;
                    value = Type::Any;
                }
                _ => {}
            },
        }
    }
    let key = if key.is_never() { Type::Any } else { key };
    let value = if value.is_never() { Type::Any } else { value };
    let inferred = Type::Hash(Box::new(key), Box::new(value));
    Some(if defer_inline_assertion {
        inferred
    } else {
        analyzer.apply_inline_assertion_in_environment_at(site, inferred, environment)
    })
}
