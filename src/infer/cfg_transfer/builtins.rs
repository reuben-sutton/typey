//! Parser-free builtin dispatch for owned CFG calls.
//!
//! Declared and inferred method signatures are consulted first by the body
//! transfer. This layer supplies the structural contracts that the recursive
//! evaluator historically obtained from Prism-backed builtin hooks.

use super::super::{Analyzer, CallArguments, Environment, Eval, OwnedCallInput};
use crate::types::Type;

pub(super) fn transfer_builtin_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
) -> Option<(Type, Option<Eval>)> {
    let name = input.name.as_str();
    if receiver.is_any() || matches!(receiver, Type::Anything) {
        let type_ = match name {
            "to_s" | "to_str" | "inspect" => Type::String,
            "nil?" | "!" | "==" | "!=" | "equal?" | "eql?" => Type::bool(),
            "object_id" | "id" | "hash" => Type::Integer,
            _ => Type::Any,
        };
        return Some((type_, None));
    }
    if receiver.is_never() {
        return Some((Type::Never, None));
    }

    let mut callback = |parameters: &[Type]| {
        analyzer.cfg_owned_block_return_type(
            input,
            parameters,
            &Type::Anything,
            values,
            environment,
        )
    };
    let result = match receiver {
        Type::String => match name {
            "to_s" | "to_str" | "inspect" | "dump" | "upcase" | "downcase" | "strip" | "lstrip"
            | "rstrip" | "chomp" | "chop" | "reverse" | "succ" | "next" | "capitalize"
            | "swapcase" | "scrub" | "force_encoding" | "+" | "*" | "delete_prefix"
            | "delete_suffix" => Some(Type::String),
            "length" | "size" | "bytesize" | "count" | "ord" => Some(Type::Integer),
            "empty?" | "start_with?" | "end_with?" | "include?" | "match?" => Some(Type::bool()),
            "to_i" | "to_int" => Some(Type::Integer),
            "to_f" => Some(Type::Float),
            "to_sym" | "intern" => Some(Type::Symbol),
            "bytes" | "codepoints" => Some(Type::Array(Box::new(Type::Integer))),
            "chars" | "lines" | "split" => Some(Type::Array(Box::new(Type::String))),
            "[]" | "slice" | "byteslice" => Some(Type::union([Type::Nil, Type::String])),
            "match" => Some(Type::union([Type::Nil, Type::named("MatchData")])),
            "=~" | "index" | "rindex" => Some(Type::union([Type::Nil, Type::Integer])),
            "gsub" | "sub" => {
                if input.block.is_some() {
                    let _ = callback(&[Type::String])?;
                }
                Some(Type::String)
            }
            "==" | "!=" | "<" | "<=" | ">" | ">=" => Some(Type::bool()),
            _ => None,
        },
        Type::Integer | Type::Float => match name {
            "+@" | "-@" | "abs" | "magnitude" | "succ" | "next" | "pred" => Some(receiver.clone()),
            "+" | "-" | "*" | "%" => Some(
                if *receiver == Type::Float || arguments.argument_types.contains(&Type::Float) {
                    Type::Float
                } else {
                    Type::Integer
                },
            ),
            "/" => Some(
                if *receiver == Type::Integer
                    && arguments
                        .argument_types
                        .iter()
                        .all(|type_| *type_ == Type::Integer)
                {
                    Type::Integer
                } else {
                    Type::Float
                },
            ),
            "<" | "<=" | ">" | ">=" | "between?" | "even?" | "odd?" | "zero?" | "finite?"
            | "nan?" | "real?" | "complex?" => Some(Type::bool()),
            "infinite?" => Some(Type::union([Type::Nil, Type::Integer])),
            "fdiv" => Some(Type::Float),
            "div" | "bit_length" | "numerator" | "denominator" | "gcd" | "lcm" => {
                Some(Type::Integer)
            }
            "divmod" => Some(Type::Array(Box::new(Type::Tuple(vec![
                Type::Integer,
                Type::Integer,
            ])))),
            "gcdlcm" | "digits" => Some(Type::Array(Box::new(Type::Integer))),
            "to_f" => Some(Type::Float),
            "to_i" | "to_int" => Some(Type::Integer),
            "to_s" | "inspect" => Some(Type::String),
            "times" | "upto" | "downto" | "step" => {
                let _ = callback(std::slice::from_ref(receiver))?;
                Some(receiver.clone())
            }
            "==" | "!=" => Some(Type::bool()),
            _ => None,
        },
        Type::Array(element) => transfer_array_builtin(analyzer, input, element, arguments),
        Type::Tuple(elements) => {
            let element = analyzer.array_element_type(&Type::Tuple(elements.clone()));
            transfer_array_builtin(analyzer, input, &element, arguments)
        }
        Type::Hash(key, value) => match name {
            "[]" | "default" | "dig" => Some(Type::union([Type::Nil, value.as_ref().clone()])),
            "[]=" => Some(
                arguments
                    .argument_types
                    .last()
                    .cloned()
                    .unwrap_or(Type::Any),
            ),
            "keys" => Some(Type::Array(Box::new(key.as_ref().clone()))),
            "values" => Some(Type::Array(Box::new(value.as_ref().clone()))),
            "length" | "size" => Some(Type::Integer),
            "empty?" | "include?" | "key?" | "has_key?" => Some(Type::bool()),
            "to_h" | "dup" | "clone" => Some(Type::Hash(key.clone(), value.clone())),
            "to_a" => Some(Type::Array(Box::new(Type::Tuple(vec![
                key.as_ref().clone(),
                value.as_ref().clone(),
            ])))),
            "==" | "!=" => Some(Type::bool()),
            _ => None,
        },
        Type::Nil | Type::True | Type::False | Type::Symbol | Type::Object | Type::Named(_, _)
            if matches!(name, "to_s" | "inspect") =>
        {
            Some(Type::String)
        }
        Type::Nil | Type::True | Type::False | Type::Symbol | Type::Object | Type::Named(_, _)
            if matches!(name, "nil?" | "!" | "==" | "!=" | "equal?" | "eql?") =>
        {
            Some(Type::bool())
        }
        Type::Nil | Type::True | Type::False | Type::Symbol | Type::Object | Type::Named(_, _)
            if matches!(name, "object_id" | "id" | "hash") =>
        {
            Some(Type::Integer)
        }
        _ => None,
    }?;
    Some((result, None))
}

fn transfer_array_builtin(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    element: &Type,
    arguments: &CallArguments<'_>,
) -> Option<Type> {
    let name = input.name.as_str();
    match name {
        "first" | "last" if arguments.argument_types.is_empty() => {
            Some(Type::union([Type::Nil, element.clone()]))
        }
        "first" | "last" | "take" | "drop" => Some(Type::Array(Box::new(element.clone()))),
        "[]" => {
            if arguments.argument_types.first() == Some(&Type::Integer) {
                Some(Type::union([Type::Nil, element.clone()]))
            } else {
                Some(Type::union([
                    Type::Nil,
                    Type::Array(Box::new(element.clone())),
                ]))
            }
        }
        "[]=" => Some(
            arguments
                .argument_types
                .last()
                .cloned()
                .unwrap_or(Type::Any),
        ),
        "length" | "size" => Some(Type::Integer),
        "empty?" | "include?" => Some(Type::bool()),
        "to_a" | "dup" | "clone" => Some(Type::Array(Box::new(element.clone()))),
        "to_h" => {
            let (key, value) = Analyzer::pair_types(element)?;
            Some(Type::Hash(Box::new(key), Box::new(value)))
        }
        "concat" | "+" | "|" => {
            let element = arguments
                .argument_types
                .iter()
                .fold(element.clone(), |type_, argument| {
                    type_.join(&analyzer.array_element_type(argument))
                });
            Some(Type::Array(Box::new(element)))
        }
        "-" | "&" | "reverse" | "rotate" | "shuffle" | "sort" => {
            Some(Type::Array(Box::new(element.clone())))
        }
        "push" | "<<" => {
            let element = arguments
                .argument_types
                .iter()
                .fold(element.clone(), |type_, argument| type_.join(argument));
            Some(Type::Array(Box::new(element)))
        }
        "join" | "pack" => Some(Type::String),
        "sample" if arguments.argument_types.is_empty() => {
            Some(Type::union([Type::Nil, element.clone()]))
        }
        "sample" => Some(Type::Array(Box::new(element.clone()))),
        "count" => Some(Type::Integer),
        "==" | "!=" => Some(Type::bool()),
        _ => None,
    }
}
