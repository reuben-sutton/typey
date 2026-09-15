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
    if matches!(receiver, Type::Anything)
        && !matches!(
            name,
            "to_s"
                | "to_str"
                | "inspect"
                | "nil?"
                | "!"
                | "=="
                | "!="
                | "equal?"
                | "eql?"
                | "object_id"
                | "id"
                | "hash"
        )
    {
        return None;
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
        if matches!(name, "<" | "<=" | ">" | ">=") {
            return Some((Type::bool(), None));
        }
        if let Type::Named(class, _) = &instance {
            if name_matches(class, "Dir") && matches!(name, "[]" | "glob") {
                return Some((Type::Array(Box::new(Type::String)), None));
            }
            if name_matches(class, "Kernel")
                && matches!(name, "abort" | "exit" | "exit!" | "fail" | "raise")
            {
                return Some((Type::Never, None));
            }
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
            if name_matches(class, "Prism")
                && matches!(name, "parse" | "parse_comments" | "parse_file")
            {
                return Some((Type::named("Prism::ParseResult"), None));
            }
        }
    }

    if name == "strongly_connected_components"
        && matches!(receiver, Type::Named(class, _) if analyzer.nominal_subtype(class, "TSort"))
    {
        let node = tsort_method_yield_type(analyzer, receiver, "tsort_each_node")
            .or_else(|| tsort_method_parameter_type(analyzer, receiver, "tsort_each_child"))
            .unwrap_or(Type::Any);
        return Some((Type::Array(Box::new(Type::Array(Box::new(node)))), None));
    }

    let mut block_result = None;
    let mut callback = |parameters: &[Type]| {
        let result = analyzer.cfg_owned_block_return_type(
            input,
            parameters,
            &Type::Anything,
            values,
            environment,
        );
        if let Some(result) = result.as_ref() {
            block_result = Some(result.clone());
        }
        result
    };
    let result = match receiver {
        Type::String => match name {
            "to_s" | "to_str" | "inspect" | "dump" | "upcase" | "downcase" | "strip" | "lstrip"
            | "rstrip" | "chomp" | "chop" | "reverse" | "succ" | "next" | "capitalize"
            | "swapcase" | "scrub" | "force_encoding" | "+" | "*" | "delete_prefix"
            | "delete_suffix" | "shellescape" | "+@" | "<<" | "encode" => Some(Type::String),
            "length" | "size" | "bytesize" | "count" | "ord" => Some(Type::Integer),
            "hash" => Some(Type::Integer),
            "empty?" | "start_with?" | "end_with?" | "include?" | "match?" | "nil?" => {
                Some(Type::bool())
            }
            "to_i" | "to_int" => Some(Type::Integer),
            "to_f" => Some(Type::Float),
            "to_r" => Some(Type::named("Rational")),
            "to_c" => Some(Type::named("Complex")),
            "to_sym" | "intern" => Some(Type::Symbol),
            "bytes" | "codepoints" => Some(Type::Array(Box::new(Type::Integer))),
            "chars" | "lines" | "split" => Some(Type::Array(Box::new(Type::String))),
            "[]" | "slice" | "byteslice" => {
                if name == "[]"
                    && arguments.argument_types.first() == Some(&Type::Integer)
                    && known_nonempty_string_receiver(analyzer, input, environment)
                {
                    Some(Type::String)
                } else {
                    Some(Type::union([Type::Nil, Type::String]))
                }
            }
            "match" => Some(Type::union([Type::Nil, Type::named("MatchData")])),
            "=~" | "index" | "rindex" => Some(Type::union([Type::Nil, Type::Integer])),
            "<=>" => {
                if arguments.argument_types.first() == Some(&Type::String) {
                    Some(Type::Integer)
                } else {
                    Some(Type::union([Type::Nil, Type::Integer]))
                }
            }
            "chomp!" | "chop!" => Some(Type::union([Type::Nil, Type::String])),
            "pluralize" | "singularize" | "underscore" | "classify" | "humanize" | "squish"
            | "camelize" => Some(Type::String),
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
            "|" | "&" | "^" | "<<" | ">>" if *receiver == Type::Integer => Some(Type::Integer),
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
            "clamp" => Some(receiver.clone()),
            "to_f" => Some(Type::Float),
            "to_r" => Some(Type::named("Rational")),
            "to_c" => Some(Type::named("Complex")),
            "real" => Some(receiver.clone()),
            "imag" => Some(Type::Integer),
            "to_i" | "to_int" => Some(Type::Integer),
            "to_s" | "inspect" => Some(Type::String),
            "times" | "upto" | "downto" | "step" => {
                if input.block.is_none() {
                    Some(Type::named("Enumerator"))
                } else {
                    let _ = callback(std::slice::from_ref(receiver))?;
                    Some(receiver.clone())
                }
            }
            "==" | "!=" => Some(Type::bool()),
            _ => None,
        },
        Type::Array(element) => transfer_array_builtin(
            analyzer,
            input,
            element,
            arguments,
            values,
            environment,
            &mut block_result,
        ),
        Type::Tuple(elements) => {
            let element = analyzer.array_element_type(&Type::Tuple(elements.clone()));
            transfer_array_builtin(
                analyzer,
                input,
                &element,
                arguments,
                values,
                environment,
                &mut block_result,
            )
        }
        Type::Hash(key, value) => match name {
            "new" => Some(Type::Hash(key.clone(), value.clone())),
            "[]" => {
                let literal_key = owned_hash_key(analyzer, input);
                Some(match (literal_key, hash_shape) {
                    (Some(key), Some(hash_shape))
                        if hash_shape.entries.contains_key(&key)
                            || hash_shape.unknown_value.is_some() =>
                    {
                        hash_shape.value_for(&key)
                    }
                    (Some(_), Some(_)) => Type::union([Type::Nil, value.as_ref().clone()]),
                    _ => Type::union([Type::Nil, value.as_ref().clone()]),
                })
            }
            "default" | "dig" => Some(Type::union([Type::Nil, value.as_ref().clone()])),
            "fetch" => {
                if let Some(default) = arguments.argument_types.get(1) {
                    Some(
                        if matches!(default, Type::Array(element) if element.is_any()) {
                            value.as_ref().clone()
                        } else {
                            value.as_ref().clone().join(default)
                        },
                    )
                } else if input.block.is_some() {
                    let callback = callback(std::slice::from_ref(key.as_ref()))?;
                    Some(
                        value
                            .as_ref()
                            .clone()
                            .join(&Analyzer::block_value_type(&callback)),
                    )
                } else {
                    Some(value.as_ref().clone())
                }
            }
            "fetch_values" => Some(Type::Array(Box::new(value.as_ref().clone()))),
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
            "any?" | "all?" | "none?" => {
                if input.block.is_some() {
                    let _ = callback(&[key.as_ref().clone(), value.as_ref().clone()])?;
                }
                Some(Type::bool())
            }
            "to_h" | "dup" | "clone" | "slice" | "except" => {
                Some(Type::Hash(key.clone(), value.clone()))
            }
            "merge" | "merge!" | "update" | "reverse_merge" => {
                let (key, value) = arguments.argument_types.iter().fold(
                    (key.as_ref().clone(), value.as_ref().clone()),
                    |(key_type, value_type), argument| match argument {
                        Type::Hash(argument_key, argument_value) => {
                            (key_type.join(argument_key), value_type.join(argument_value))
                        }
                        _ => (key_type, value_type),
                    },
                );
                Some(Type::Hash(Box::new(key), Box::new(value)))
            }
            "compact" => Some(Type::Hash(
                key.clone(),
                Box::new(value.as_ref().clone().without(&Type::Nil)),
            )),
            "invert" => Some(Type::Hash(value.clone(), key.clone())),
            "sort" => Some(Type::Array(Box::new(Type::Tuple(vec![
                key.as_ref().clone(),
                value.as_ref().clone(),
            ])))),
            "values_at" => Some(Type::Array(Box::new(value.as_ref().clone()))),
            "to_a" => Some(Type::Array(Box::new(Type::Tuple(vec![
                key.as_ref().clone(),
                value.as_ref().clone(),
            ])))),
            "==" | "!=" => Some(Type::bool()),
            _ => None,
        },
        Type::Named(class, _arguments) if name_matches(class, "ENV") => match name {
            "[]" | "fetch" | "[]=" => Some(Type::union([Type::Nil, Type::String])),
            "to_h" => Some(Type::Hash(Box::new(Type::String), Box::new(Type::String))),
            _ => None,
        },
        Type::Named(class, _arguments)
            if name_matches(class, "YAML") || name_matches(class, "Psych") =>
        {
            match name {
                "dump" => Some(Type::String),
                "load" | "load_file" => Some(Type::union([Type::Nil, Type::Object])),
                _ => None,
            }
        }
        Type::Named(class, _) if name_matches(class, "OptionParser") => match name {
            "on" => {
                if input.block.is_some() {
                    let option_type = arguments
                        .argument_types
                        .iter()
                        .skip(1)
                        .find_map(option_parser_option_type)
                        .unwrap_or(Type::Any);
                    let _ = callback(std::slice::from_ref(&option_type))?;
                }
                Some(Type::named("OptionParser"))
            }
            "parse!" => Some(Type::Array(Box::new(Type::String))),
            _ => None,
        },
        Type::Named(class, _)
            if name_matches(class, "Parser::Source::Map")
                || name_matches(class, "Parser::Source::Range") =>
        {
            match name {
                "line" | "column" | "first_line" | "first_column" | "last_line" | "last_column" => {
                    Some(Type::Integer)
                }
                _ => None,
            }
        }
        Type::Named(class, _) if name_matches(class, "Parser::AST::Node") => match name {
            "location" | "loc" => Some(Type::named("Parser::Source::Map")),
            _ => None,
        },
        Type::Named(class, _) if name_matches(class, "Regexp") => match name {
            "match" => Some(Type::union([Type::Nil, Type::named("MatchData")])),
            "match?" | "===" => Some(Type::bool()),
            "=~" | "~" => Some(Type::union([Type::Nil, Type::Integer])),
            "source" | "to_s" => Some(Type::String),
            "options" => Some(Type::Integer),
            "encoding" => Some(Type::named("Encoding")),
            _ => None,
        },
        Type::Named(class, type_arguments) if name_matches(class, "Range") => {
            let begin = type_arguments.first().cloned().unwrap_or(Type::Any);
            let end = type_arguments.get(1).cloned().unwrap_or(Type::Any);
            let element = begin.join(&end).without(&Type::Nil);
            let element = if element.is_never() {
                Type::Any
            } else {
                element
            };
            match name {
                "begin" => Some(begin),
                "end" => Some(end),
                "exclude_end?" => Some(Type::bool()),
                "include?" | "cover?" | "member?" => Some(Type::bool()),
                "to_a" => Some(Type::Array(Box::new(element))),
                "each" | "step" => {
                    if input.block.is_none() {
                        Some(Type::named("Enumerator"))
                    } else {
                        let _ = callback(std::slice::from_ref(&element))?;
                        Some(Type::Named(class.clone(), type_arguments.clone()))
                    }
                }
                "first" => Some(begin),
                "last" => Some(end),
                "to_s" | "inspect" => Some(Type::String),
                _ => None,
            }
        }
        Type::Named(class, type_arguments) if name_matches(class, "Set") => {
            let element = type_arguments.first().cloned().unwrap_or(Type::Any);
            match name {
                "empty?" | "include?" | "member?" | "intersect?" | "any?" | "all?" | "none?" => {
                    if input.block.is_some() {
                        let _ = callback(std::slice::from_ref(&element))?;
                    }
                    Some(Type::bool())
                }
                "each" => {
                    if input.block.is_none() {
                        Some(Type::named("Enumerator"))
                    } else {
                        let _ = callback(std::slice::from_ref(&element))?;
                        Some(Type::Named(class.clone(), type_arguments.clone()))
                    }
                }
                "map" | "collect" => {
                    if input.block.is_none() {
                        Some(Type::named("Enumerator"))
                    } else {
                        let callback = callback(std::slice::from_ref(&element))?;
                        Some(Type::Array(Box::new(Analyzer::block_value_type(&callback))))
                    }
                }
                "select" | "filter" | "reject" => {
                    if input.block.is_none() {
                        Some(Type::named("Enumerator"))
                    } else {
                        let _ = callback(std::slice::from_ref(&element))?;
                        Some(Type::Named(class.clone(), type_arguments.clone()))
                    }
                }
                "-" => Some(Type::Named(class.clone(), type_arguments.clone())),
                "|" | "&" | "+" => {
                    let other = arguments
                        .argument_types
                        .first()
                        .map(|argument| analyzer.array_element_type(argument))
                        .unwrap_or(Type::Any);
                    Some(Type::Named(class.clone(), vec![element.join(&other)]))
                }
                "to_a" => Some(Type::Array(Box::new(element))),
                _ => None,
            }
        }
        Type::Named(class, arguments)
            if name_matches(class, "Enumerator") || name_matches(class, "Enumerable") =>
        {
            match name {
                "each" => {
                    if input.block.is_none() {
                        Some(Type::named("Enumerator"))
                    } else {
                        let element = arguments.first().cloned().unwrap_or(Type::Any);
                        let _ = callback(std::slice::from_ref(&element))?;
                        Some(Type::Named(class.clone(), arguments.clone()))
                    }
                }
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
        Type::Symbol if matches!(name, "to_sym" | "intern") => Some(Type::Symbol),
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
    Some((result, block_result))
}

fn tsort_method_yield_type(analyzer: &Analyzer<'_>, receiver: &Type, name: &str) -> Option<Type> {
    analyzer
        .receiver_method_key(None, receiver, name, &super::super::Environment::default())
        .and_then(|key| analyzer.resolve_method_key(&key))
        .and_then(|key| analyzer.declarations.methods.get(&key))
        .and_then(|method| method.yield_params.first().cloned().flatten())
}

fn tsort_method_parameter_type(
    analyzer: &Analyzer<'_>,
    receiver: &Type,
    name: &str,
) -> Option<Type> {
    analyzer
        .receiver_method_key(None, receiver, name, &super::super::Environment::default())
        .and_then(|key| analyzer.resolve_method_key(&key))
        .and_then(|key| analyzer.declarations.methods.get(&key))
        .and_then(|method| method.params.first().cloned().flatten())
}

fn option_parser_option_type(type_: &Type) -> Option<Type> {
    let type_ = Analyzer::class_object_value_type(type_).unwrap_or_else(|| type_.clone());
    match type_ {
        Type::Named(name, _) if name_matches(&name, "Array") => {
            Some(Type::Array(Box::new(Type::String)))
        }
        Type::String => Some(Type::String),
        Type::Integer => Some(Type::Integer),
        Type::Float => Some(Type::Float),
        Type::True | Type::False => Some(Type::bool()),
        Type::Named(name, _) if name_matches(&name, "TrueClass") => Some(Type::bool()),
        Type::Named(name, _) if name_matches(&name, "FalseClass") => Some(Type::bool()),
        _ => None,
    }
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
    values: &[Option<Type>],
    environment: &mut Environment,
    block_result: &mut Option<Eval>,
) -> Option<Type> {
    let name = input.name.as_str();
    let flattened_element = analyzer.flattened_array_element_type(element);
    let argument_elements = arguments
        .argument_types
        .iter()
        .map(|argument| analyzer.array_element_type(argument))
        .collect::<Vec<_>>();
    let mut callback = |parameters: &[Type]| {
        let result = analyzer.cfg_owned_block_return_type(
            input,
            parameters,
            &Type::Anything,
            values,
            environment,
        );
        if let Some(result) = result.as_ref() {
            *block_result = Some(result.clone());
        }
        result
    };
    match name {
        "new" => Some(Type::Array(Box::new(element.clone()))),
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
            } else if owned_range_starts_at_zero(analyzer, input) {
                // `Array#[]` is nilable for an arbitrary range, but a range
                // beginning at zero always returns an array (possibly
                // empty). This is the contract used by Active Support's
                // `Array#to` implementation.
                Some(Type::Array(Box::new(element.clone())))
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
        "any?" | "all?" | "none?" => {
            if input.block.is_some() {
                let _ = callback(std::slice::from_ref(element))?;
            }
            Some(Type::bool())
        }
        "inspect" | "to_s" => Some(Type::String),
        "compact" => Some(Type::Array(Box::new(element.without(&Type::Nil)))),
        "to_a" | "dup" | "clone" => Some(Type::Array(Box::new(element.clone()))),
        "flatten" => Some(Type::Array(Box::new(flattened_element))),
        "uniq" => Some(Type::Array(Box::new(element.clone()))),
        "to_set" => Some(Type::Named("T::Set".to_owned(), vec![element.clone()])),
        "to_h" => {
            let (key, value) = Analyzer::pair_types(element)?;
            Some(Type::Hash(Box::new(key), Box::new(value)))
        }
        "fetch" => {
            if let Some(default) = arguments.argument_types.get(1) {
                Some(
                    if matches!(default, Type::Array(default_element) if default_element.is_any()) {
                        element.clone()
                    } else {
                        element.join(default)
                    },
                )
            } else if input.block.is_some() {
                let callback = analyzer.cfg_owned_block_return_type(
                    input,
                    std::slice::from_ref(&Type::Integer),
                    &Type::Anything,
                    values,
                    environment,
                )?;
                Some(element.join(&Analyzer::block_value_type(&callback)))
            } else {
                Some(element.clone())
            }
        }
        "at" => Some(Type::union([Type::Nil, element.clone()])),
        "shift" | "pop" if arguments.argument_types.is_empty() => {
            Some(Type::union([Type::Nil, element.clone()]))
        }
        "shift" | "pop" => Some(Type::Array(Box::new(element.clone()))),
        "values_at" => Some(Type::Array(Box::new(element.clone()))),
        "grep" => {
            let filtered = arguments
                .argument_types
                .first()
                .and_then(Analyzer::class_object_value_type)
                .map(|expected| analyzer.meet_predicate_type(element, &expected))
                .unwrap_or_else(|| element.clone());
            Some(Type::Array(Box::new(filtered)))
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
            for (index, argument) in arguments.argument_types.iter().enumerate() {
                let argument_for_check = arguments
                    .literal_tuple_arguments
                    .get(index)
                    .and_then(Option::as_ref)
                    .unwrap_or(argument);
                if !analyzer.is_assignable(argument_for_check, element) {
                    let site = arguments
                        .argument_sites
                        .get(index)
                        .copied()
                        .unwrap_or(input.site);
                    let actual = owned_literal_type_description(analyzer, site, argument_for_check);
                    analyzer.error_at(site, format!("Expected `{element}` but found `{actual}`"));
                }
            }
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
        "count" => {
            if input.block.is_some() {
                let _ = callback(std::slice::from_ref(element))?;
            }
            Some(Type::Integer)
        }
        "select!" | "filter!" | "reject!" => {
            if input.block.is_none() {
                Some(Type::named("Enumerator"))
            } else {
                let _ = callback(std::slice::from_ref(element))?;
                Some(Type::union([
                    Type::Nil,
                    Type::Array(Box::new(element.clone())),
                ]))
            }
        }
        "fill" | "replace" | "clear" | "unshift" | "insert" | "reverse!" | "rotate!"
        | "shuffle!" | "sort!" => Some(Type::Array(Box::new(element.clone()))),
        "uniq!" => Some(Type::union([
            Type::Nil,
            Type::Array(Box::new(element.clone())),
        ])),
        "bsearch" => {
            if input.block.is_none() {
                Some(Type::named("Enumerator"))
            } else {
                let _ = callback(std::slice::from_ref(element))?;
                Some(Type::union([Type::Nil, element.clone()]))
            }
        }
        "min_by" | "max_by" => {
            if input.block.is_none() {
                Some(Type::named("Enumerator"))
            } else {
                let _ = callback(std::slice::from_ref(element))?;
                Some(Type::union([Type::Nil, element.clone()]))
            }
        }
        "combination" | "repeated_combination" | "permutation" | "repeated_permutation" => {
            if input.block.is_none() {
                Some(Type::Named(
                    "T::Enumerator".to_owned(),
                    vec![Type::Array(Box::new(element.clone()))],
                ))
            } else {
                let expected = Type::Array(Box::new(element.clone()));
                let _ = callback(std::slice::from_ref(&expected))?;
                Some(Type::Array(Box::new(element.clone())))
            }
        }
        "product" => {
            let mut tuple = vec![element.clone()];
            tuple.extend(argument_elements.clone());
            if input.block.is_none() {
                Some(Type::Array(Box::new(Type::Tuple(tuple))))
            } else {
                let expected = Type::Array(Box::new(Type::Tuple(tuple)));
                let _ = callback(std::slice::from_ref(&expected))?;
                Some(Type::Array(Box::new(element.clone())))
            }
        }
        "zip" => {
            let mut tuple = vec![element.clone()];
            // Arrays are allowed to have different lengths. Ruby pads a
            // missing element from a shorter argument with nil, so the
            // element type of every additional tuple position is nilable.
            tuple.extend(
                argument_elements
                    .into_iter()
                    .map(|argument| Type::union([Type::Nil, argument])),
            );
            Some(Type::Array(Box::new(Type::Tuple(tuple))))
        }
        "sum" => {
            let element = if input.block.is_some() {
                let callback = callback(std::slice::from_ref(element))?;
                Analyzer::block_value_type(&callback)
            } else {
                element.clone()
            };
            Some(Analyzer::numeric_sum_type(
                &element,
                arguments.argument_types.first(),
            ))
        }
        "==" | "!=" => Some(Type::bool()),
        _ => None,
    }
}

fn owned_literal_type_description(
    analyzer: &Analyzer<'_>,
    site: super::super::SourceSite,
    type_: &Type,
) -> String {
    let Some(expression) = site
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
    else {
        return type_.to_string();
    };
    match (&expression.kind, type_) {
        (hir::ExprKind::Literal(hir::Literal::String(value)), Type::String) => {
            format!("String(\"{value}\")")
        }
        (hir::ExprKind::Literal(hir::Literal::Integer(value)), Type::Integer) => {
            format!("Integer({value})")
        }
        _ => type_.to_string(),
    }
}

fn owned_range_starts_at_zero(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> bool {
    let Some(expression) = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
    else {
        return false;
    };
    let hir::ExprKind::Call(call) = &expression.kind else {
        return false;
    };
    let Some(hir::Argument::Positional(argument)) = call.arguments.first() else {
        return false;
    };
    let Some(expression) = analyzer.program.hir_program.expression(*argument) else {
        return false;
    };
    let hir::ExprKind::Range {
        left: Some(left), ..
    } = expression.kind
    else {
        return false;
    };
    matches!(
        analyzer.program.hir_program.expression(left).map(|expression| &expression.kind),
        Some(hir::ExprKind::Literal(hir::Literal::Integer(value))) if value == "0"
    )
}

pub(super) fn known_nonempty_string_receiver(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    environment: &Environment,
) -> bool {
    let Some(expression) = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
    else {
        return false;
    };
    let hir::ExprKind::Call(call) = &expression.kind else {
        return false;
    };
    let hir::Receiver::Explicit(receiver) = call.receiver else {
        return false;
    };
    let Some(receiver) = analyzer.program.hir_program.expression(receiver) else {
        return false;
    };
    let hir::ExprKind::Read(hir::Read::Local(local)) = &receiver.kind else {
        return false;
    };
    analyzer
        .program
        .hir_program
        .local_name(*local)
        .is_some_and(|name| environment.known_nonempty_string(name.as_str()))
}
