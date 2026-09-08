//! Parser-free structural models for collection calls in owned CFG transfer.
//!
//! These are deliberately separate from `BodyTransfer`: the body walker only
//! routes a call, while this module owns the type-level collection contracts
//! and callback shape. RBIs take precedence; these models are used when the
//! core collection declaration is absent or has no usable return contract.

use super::super::{Analyzer, Environment, Eval, OwnedCallInput};
use crate::cfg;
use crate::types::Type;
use std::slice;

pub(super) fn transfer_collection_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    values: &[Option<Type>],
    environment: &mut Environment,
) -> Option<(Type, Option<Eval>)> {
    let element = match receiver {
        Type::Array(element) => element.as_ref().clone(),
        Type::Tuple(elements) => analyzer.array_element_type(&Type::Tuple(elements.clone())),
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
            | "select"
            | "filter"
            | "reject"
    );
    let block_is_nil = matches!(input.block, Some(cfg::BlockOperand::Passed(value))
        if values.get(value.0 as usize).and_then(Option::as_ref).is_some_and(Type::is_nil));
    if input.block.is_none() || block_is_nil {
        return requires_block.then(|| (Type::named("Enumerator"), None));
    }

    let callback = analyzer.cfg_owned_block_return_type(
        input,
        slice::from_ref(&element),
        &Type::Anything,
        values,
        environment,
    )?;
    let callback_type = Analyzer::block_value_type(&callback);
    let result = match name {
        "map" | "collect" | "map!" | "collect!" => Type::Array(Box::new(callback_type)),
        "flat_map" => Type::Array(Box::new(analyzer.flat_map_element_type(&callback_type))),
        "filter_map" => Type::Array(Box::new(callback_type.truthy_part())),
        "each" | "select" | "filter" | "reject" => Type::Array(Box::new(element)),
        _ => return None,
    };
    Some((result, Some(callback)))
}
