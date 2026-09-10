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
            | "delete_if"
            | "each_with_object"
            | "each_with_index"
            | "each_index"
            | "find"
            | "detect"
            | "find_index"
            | "group_by"
            | "partition"
            | "take_while"
            | "drop_while"
            | "sort_by"
            | "sort_by!"
            | "sort"
            | "min_by"
            | "max_by"
            | "any?"
            | "all?"
            | "none?"
            | "count"
            | "transform_keys"
            | "transform_values"
    ) && match &kind {
        CollectionKind::Array => !matches!(name, "each_pair" | "each_key" | "each_value"),
        CollectionKind::Hash(_, _) => true,
    };
    let block_is_nil = matches!(input.block, Some(cfg::BlockOperand::Passed(value))
        if values.get(value.0 as usize).and_then(Option::as_ref).is_some_and(Type::is_nil));
    if input.block.is_none() || block_is_nil {
        if matches!(name, "any?" | "all?" | "none?" | "count") {
            return None;
        }
        if name == "sort" {
            return None;
        }
        if name == "to_h" {
            return None;
        }
        return requires_block.then(|| (Type::named("Enumerator"), None));
    }

    let callback_parameters = if name == "each_with_object" {
        vec![parameters[0].clone(), arguments_first_or_any(input, values)]
    } else if name == "each_with_index" {
        vec![parameters[0].clone(), Type::Integer]
    } else if name == "each_index" {
        vec![Type::Integer]
    } else if name == "transform_keys" {
        vec![parameters[0].clone()]
    } else if name == "transform_values" {
        vec![parameters[1].clone()]
    } else {
        parameters.clone()
    };
    let (callback, callback_environment) = if name == "each_with_object" {
        analyzer.cfg_owned_block_return_type_with_environment(
            input,
            &callback_parameters,
            &Type::Anything,
            values,
            environment,
        )?
    } else {
        let callback = analyzer.cfg_owned_block_return_type(
            input,
            &callback_parameters,
            &Type::Anything,
            values,
            environment,
        )?;
        (callback, environment.clone())
    };
    let callback_type = Analyzer::block_value_type(&callback);
    let result = match name {
        "map" | "collect" | "map!" | "collect!"
            if matches!(kind, CollectionKind::Array | CollectionKind::Hash(_, _)) =>
        {
            Type::Array(Box::new(callback_type))
        }
        "flat_map" => Type::Array(Box::new(analyzer.flat_map_element_type(&callback_type))),
        "filter_map" => Type::Array(Box::new(callback_type.truthy_part())),
        "each" | "select" | "filter" | "reject" | "delete_if" => match kind {
            CollectionKind::Array => Type::Array(Box::new(parameters[0].clone())),
            CollectionKind::Hash(key, value) => Type::Hash(Box::new(key), Box::new(value)),
        },
        "each_with_object" => {
            each_with_object_result(analyzer, input, values, &callback_environment)
        }
        "each_with_index" | "each_index" => match kind {
            CollectionKind::Array => Type::Array(Box::new(parameters[0].clone())),
            CollectionKind::Hash(key, value) => Type::Hash(Box::new(key), Box::new(value)),
        },
        "find" | "detect" | "min_by" | "max_by" => match kind {
            CollectionKind::Array => Type::union([Type::Nil, parameters[0].clone()]),
            CollectionKind::Hash(key, value) => {
                Type::union([Type::Nil, Type::Tuple(vec![key.clone(), value.clone()])])
            }
        },
        "find_index" => Type::union([Type::Nil, Type::Integer]),
        "any?" | "all?" | "none?" => Type::bool(),
        "count" => Type::Integer,
        "to_h" => {
            let (key, value) = Analyzer::pair_types(&callback_type)?;
            Type::Hash(Box::new(key), Box::new(value))
        }
        "group_by" => Type::Hash(
            Box::new(callback_type),
            Box::new(Type::Array(Box::new(parameters[0].clone()))),
        ),
        "partition" => Type::Array(Box::new(Type::Array(Box::new(parameters[0].clone())))),
        "take_while" | "drop_while" | "sort_by" | "sort_by!" => match kind {
            CollectionKind::Array => Type::Array(Box::new(parameters[0].clone())),
            CollectionKind::Hash(key, value) => {
                Type::Array(Box::new(Type::Tuple(vec![key, value])))
            }
        },
        "sort" => match kind {
            CollectionKind::Array => Type::Array(Box::new(parameters[0].clone())),
            CollectionKind::Hash(key, value) => {
                Type::Array(Box::new(Type::Tuple(vec![key, value])))
            }
        },
        "transform_keys" => match kind {
            CollectionKind::Array => return None,
            CollectionKind::Hash(_, value) => Type::Hash(Box::new(callback_type), Box::new(value)),
        },
        "transform_values" => match kind {
            CollectionKind::Array => return None,
            CollectionKind::Hash(key, _) => Type::Hash(Box::new(key), Box::new(callback_type)),
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

fn each_with_object_result(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    values: &[Option<Type>],
    callback_environment: &Environment,
) -> Type {
    let Some(cfg::BlockOperand::Inline(closure)) = input.block.as_ref() else {
        return arguments_first_or_any(input, values);
    };
    let Some(name) = analyzer
        .program
        .hir_program
        .closure(*closure)
        .and_then(|closure| closure.parameters.parameters.get(1))
        .and_then(|parameter| parameter.name.as_ref())
        .map(|name| name.as_str())
    else {
        return arguments_first_or_any(input, values);
    };
    let refined = callback_environment.get(name);
    if refined.is_any() {
        arguments_first_or_any(input, values)
    } else {
        refined
    }
}

fn arguments_first_or_any(input: &OwnedCallInput, values: &[Option<Type>]) -> Type {
    let Some(crate::cfg::ArgumentOperand::Positional(value)) = input.arguments.first() else {
        return Type::Any;
    };
    values
        .get(value.0 as usize)
        .and_then(Option::as_ref)
        .cloned()
        .unwrap_or(Type::Any)
}
