//! Parser-free builtin dispatch for owned CFG calls.
//!
//! Declared and inferred method signatures are consulted first by the body
//! transfer. This layer supplies the structural contracts that the recursive
//! evaluator historically obtained from Prism-backed builtin hooks.

use super::super::hash_shape::{HashKey, HashShape};
use super::super::{name_matches, Analyzer, CallArguments, Environment, Eval, OwnedCallInput};
use crate::types::Type;
use crate::{hir, signature};

pub(super) fn transfer_builtin_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
    hash_shape: Option<&HashShape>,
) -> Option<(Type, Option<Eval>)> {
    let name = input.name.as_str();
    if let Type::Union(members) = receiver {
        if input.block.is_none() {
            let mut result = Type::Never;
            for member in members {
                let (type_, _) = transfer_builtin_call(
                    analyzer,
                    input,
                    member,
                    arguments,
                    values,
                    environment,
                    hash_shape,
                )?;
                result = result.join(&type_);
            }
            return (!result.is_never()).then_some((result, None));
        }
        if matches!(name, "map" | "collect") {
            let mut element = Type::Never;
            for member in members {
                let member_element = match member {
                    Type::Array(element) => element.as_ref().clone(),
                    Type::Tuple(elements) => {
                        analyzer.array_element_type(&Type::Tuple(elements.clone()))
                    }
                    Type::Named(class, arguments) if name_matches(class, "Enumerator") => {
                        arguments.first().cloned().unwrap_or(Type::Any)
                    }
                    _ => return None,
                };
                element = element.join(&member_element);
            }
            let callback = analyzer.cfg_owned_block_return_type(
                input,
                std::slice::from_ref(&element),
                &Type::Anything,
                values,
                environment,
            )?;
            return Some((
                Type::Array(Box::new(Analyzer::block_value_type(&callback))),
                Some(callback),
            ));
        }
    }
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
    if name == "[]" {
        if let Type::Named(record, _) = receiver {
            if let Some(key) = owned_inline_record_key(analyzer, input) {
                if let Some(type_) = signature::parse_inline_record_field(record, &key) {
                    return Some((type_, None));
                }
            }
        }
    }

    if let Some(instance) = Analyzer::class_object_instance_type(receiver) {
        if let Type::Named(class, _) = &instance {
            if name_matches(class, "ActiveSupport::Inflector") {
                return Some((
                    match name {
                        "classify" | "camelize" | "underscore" | "humanize" => Type::String,
                        "inflections" => Type::named("ActiveSupport::Inflector::Inflections"),
                        _ => return None,
                    },
                    None,
                ));
            }
        }
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
            | "delete_suffix" | "shellescape" | "+@" | "<<" => Some(Type::String),
            "length" | "size" | "bytesize" | "count" | "ord" => Some(Type::Integer),
            "hash" => Some(Type::Integer),
            "empty?" | "start_with?" | "end_with?" | "include?" | "match?" | "nil?" => {
                Some(Type::bool())
            }
            "to_i" | "to_int" => Some(Type::Integer),
            "to_f" => Some(Type::Float),
            "to_sym" | "intern" => Some(Type::Symbol),
            "bytes" | "codepoints" => Some(Type::Array(Box::new(Type::Integer))),
            "chars" | "lines" | "split" => Some(Type::Array(Box::new(Type::String))),
            "[]" | "slice" | "byteslice" => Some(Type::union([Type::Nil, Type::String])),
            "match" => Some(Type::union([Type::Nil, Type::named("MatchData")])),
            "=~" | "index" | "rindex" => Some(Type::union([Type::Nil, Type::Integer])),
            "chomp!" | "chop!" => Some(Type::union([Type::Nil, Type::String])),
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
            "round" | "ceil" | "floor" | "truncate" => {
                Some(if arguments.argument_types.is_empty() {
                    Type::Integer
                } else {
                    Type::Float
                })
            }
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
            "[]" => {
                let literal_key = owned_hash_key(analyzer, input);
                Some(match (literal_key, hash_shape) {
                    (Some(key), Some(hash_shape)) => hash_shape.value_for(&key),
                    _ => Type::union([Type::Nil, value.as_ref().clone()]),
                })
            }
            "default" | "dig" => Some(Type::union([Type::Nil, value.as_ref().clone()])),
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
        Type::Named(class, _arguments) if name_matches(class, "ENV") => match name {
            "[]" | "fetch" | "[]=" => Some(Type::union([Type::Nil, Type::String])),
            _ => None,
        },
        Type::Named(class, arguments) if name_matches(class, "Set") => match name {
            "empty?" | "include?" | "member?" | "intersect?" => Some(Type::bool()),
            "to_a" => Some(Type::Array(Box::new(
                arguments.first().cloned().unwrap_or(Type::Any),
            ))),
            _ => None,
        },
        Type::Named(class, arguments)
            if name_matches(class, "Enumerator") || name_matches(class, "Enumerable") =>
        {
            match name {
                "map" | "collect" => {
                    if input.block.is_none() {
                        Some(Type::Named(class.clone(), arguments.clone()))
                    } else {
                        let element = arguments.first().cloned().unwrap_or(Type::Any);
                        let callback = callback(std::slice::from_ref(&element))?;
                        Some(Type::Array(Box::new(Analyzer::block_value_type(&callback))))
                    }
                }
                "entries" | "to_a" => Some(Type::Array(Box::new(
                    arguments.first().cloned().unwrap_or(Type::Any),
                ))),
                _ => None,
            }
        }
        Type::Symbol if name == "name" => Some(Type::String),
        Type::Nil | Type::True | Type::False | Type::Object | Type::Named(_, _)
            if matches!(name, "to_s" | "inspect") =>
        {
            Some(Type::String)
        }
        Type::Nil | Type::True | Type::False | Type::Object | Type::Named(_, _)
            if matches!(
                name,
                "nil?"
                    | "is_a?"
                    | "kind_of?"
                    | "instance_of?"
                    | "!"
                    | "=="
                    | "!="
                    | "equal?"
                    | "eql?"
                    | "==="
            ) =>
        {
            Some(Type::bool())
        }
        Type::Nil | Type::True | Type::False | Type::Object | Type::Named(_, _)
            if matches!(name, "object_id" | "id" | "hash") =>
        {
            Some(Type::Integer)
        }
        _ => None,
    }?;
    Some((result, None))
}

fn owned_inline_record_key(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> Option<String> {
    let expression = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))?;
    let hir::ExprKind::Call(call) = &expression.kind else {
        return None;
    };
    let hir::Argument::Positional(argument) = call.arguments.first()? else {
        return None;
    };
    let expression = analyzer.program.hir_program.expression(*argument)?;
    match &expression.kind {
        hir::ExprKind::Literal(hir::Literal::Symbol(name))
        | hir::ExprKind::Literal(hir::Literal::String(name)) => Some(name.clone()),
        _ => None,
    }
}

pub(super) fn owned_symbol_arguments(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
) -> Option<(String, String)> {
    let expression = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))?;
    let hir::ExprKind::Call(call) = &expression.kind else {
        return None;
    };
    let mut symbols = call.arguments.iter().filter_map(|argument| {
        let hir::Argument::Positional(argument) = argument else {
            return None;
        };
        let expression = analyzer.program.hir_program.expression(*argument)?;
        match &expression.kind {
            hir::ExprKind::Literal(hir::Literal::Symbol(name))
            | hir::ExprKind::Literal(hir::Literal::String(name)) => Some(name.clone()),
            _ => None,
        }
    });
    Some((symbols.next()?, symbols.next()?))
}

pub(super) fn owned_hash_key(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> Option<HashKey> {
    let expression = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))?;
    let hir::ExprKind::Call(call) = &expression.kind else {
        return None;
    };
    let hir::Argument::Positional(argument) = call.arguments.first()? else {
        return None;
    };
    super::super::hash_shape::literal_key(&analyzer.program.hir_program, *argument)
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
        "min" | "max" if arguments.argument_types.is_empty() => {
            Some(Type::union([Type::Nil, element.clone()]))
        }
        "min" | "max" => Some(Type::Array(Box::new(element.clone()))),
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
        "<=>" => {
            Some(
                if arguments.argument_types.first().is_some_and(|other| {
                    analyzer.definitely_comparable_array_element(element, other)
                }) {
                    Type::Integer
                } else {
                    Type::union([Type::Nil, Type::Integer])
                },
            )
        }
        "[]=" => Some(
            arguments
                .argument_types
                .last()
                .cloned()
                .unwrap_or(Type::Any),
        ),
        "length" | "size" => Some(Type::Integer),
        "empty?" | "include?" | "intersect?" => Some(Type::bool()),
        "to_a" | "dup" | "clone" => Some(Type::Array(Box::new(element.clone()))),
        "to_set" => Some(Type::Named("Set".to_owned(), vec![element.clone()])),
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
        "push" | "<<" | "prepend" => {
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
