//! Parser-free structural models for collection calls in owned CFG transfer.
//!
//! These are deliberately separate from `BodyTransfer`: the body walker only
//! routes a call, while this module owns the type-level collection contracts
//! and callback shape. RBIs take precedence; these models are used when the
//! core collection declaration is absent or has no usable return contract.

use super::super::{Analyzer, Environment, Eval, OwnedCallInput};
use crate::cfg;
use crate::types::Type;

pub(super) fn transfer_collection_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    values: &[Option<Type>],
    environment: &mut Environment,
) -> Option<(Type, Option<Eval>)> {
    enum CollectionKind {
        Array,
        Hash(Type, Type),
    }
    let (parameters, kind) = match receiver {
        Type::Array(element) => (vec![element.as_ref().clone()], CollectionKind::Array),
        Type::Tuple(elements) => (
            vec![analyzer.array_element_type(&Type::Tuple(elements.clone()))],
            CollectionKind::Array,
        ),
        Type::Hash(key, value) => (
            vec![key.as_ref().clone(), value.as_ref().clone()],
            CollectionKind::Hash(key.as_ref().clone(), value.as_ref().clone()),
        ),
        _ => return None,
    };
    let name = input.name.as_str();
    let requires_block = matches!(
        name,
        "map"
            | "collect"
            | "map!"
            | "collect!"
            | "flat_map"
            | "filter_map"
            | "each"
            | "each_pair"
            | "each_key"
            | "each_value"
            | "select"
            | "filter"
            | "reject"
    ) && match &kind {
        CollectionKind::Array => !matches!(name, "each_pair" | "each_key" | "each_value"),
        CollectionKind::Hash(_, _) => true,
    };
    let block_is_nil = matches!(input.block, Some(cfg::BlockOperand::Passed(value))
        if values.get(value.0 as usize).and_then(Option::as_ref).is_some_and(Type::is_nil));
    if input.block.is_none() || block_is_nil {
        return requires_block.then(|| (Type::named("Enumerator"), None));
    }

    let callback = analyzer.cfg_owned_block_return_type(
        input,
        &parameters,
        &if parameters.len() > 1 {
            Type::Tuple(vec![Type::Any; parameters.len()])
        } else {
            Type::Anything
        },
        values,
        environment,
    )?;
    let callback_type = Analyzer::block_value_type(&callback);
    let result = match name {
        "map" | "collect" | "map!" | "collect!"
            if matches!(kind, CollectionKind::Array | CollectionKind::Hash(_, _)) =>
        {
            Type::Array(Box::new(callback_type))
        }
        "flat_map" => Type::Array(Box::new(analyzer.flat_map_element_type(&callback_type))),
        "filter_map" => Type::Array(Box::new(callback_type.truthy_part())),
        "each" | "select" | "filter" | "reject" => match kind {
            CollectionKind::Array => Type::Array(Box::new(parameters[0].clone())),
            CollectionKind::Hash(key, value) => Type::Hash(Box::new(key), Box::new(value)),
        },
        "each_pair" => match kind {
            CollectionKind::Hash(key, value) => Type::Hash(Box::new(key), Box::new(value)),
            CollectionKind::Array => return None,
        },
        "each_key" | "each_value" => match kind {
            CollectionKind::Hash(key, value) => Type::Hash(Box::new(key), Box::new(value)),
            CollectionKind::Array => return None,
        },
        _ => return None,
    };
    Some((result, Some(callback)))
}
