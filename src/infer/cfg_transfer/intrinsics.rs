//! Parser-free Sorbet intrinsic contracts for owned CFG calls.

use super::super::{Analyzer, CallArguments, OwnedCallInput, UntypedOrigin};
use crate::types::Type;

pub(super) fn transfer_intrinsic_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
) -> Option<(Type, UntypedOrigin)> {
    let Type::Named(name, _) = receiver else {
        return None;
    };
    if name != "T" {
        return None;
    }
    let actual = arguments
        .argument_types
        .first()
        .cloned()
        .unwrap_or(Type::Any);
    let value_type =
        |type_: &Type| Analyzer::class_object_value_type(type_).unwrap_or_else(|| type_.clone());
    let result = match input.name.as_str() {
        "must" => (actual.without(&Type::Nil), UntypedOrigin::Propagated),
        "unsafe" => (Type::Any, UntypedOrigin::Unsafe),
        "cast" | "let" | "bind" => {
            let expected = arguments
                .argument_types
                .get(1)
                .map(value_type)
                .unwrap_or(Type::Any);
            if input.name.as_str() == "let"
                && !expected.is_any()
                && !analyzer.is_assignable(&actual, &expected)
            {
                analyzer.error_at(
                    input.site,
                    format!("Expected `{expected}` but found `{actual}`"),
                );
            }
            (expected, UntypedOrigin::Propagated)
        }
        "assert_type!" => {
            let expected = arguments
                .argument_types
                .get(1)
                .map(value_type)
                .unwrap_or(Type::Any);
            if !expected.is_any() && !analyzer.is_assignable(&actual, &expected) {
                analyzer.error_at(
                    input.site,
                    format!("Expected `{expected}` but found `{actual}`"),
                );
            }
            (actual, UntypedOrigin::Propagated)
        }
        "nilable" => (
            Type::union([Type::Nil, value_type(&actual)]),
            UntypedOrigin::Propagated,
        ),
        "any" => (
            Type::union(arguments.argument_types.iter().map(value_type)),
            UntypedOrigin::Propagated,
        ),
        "all" => (
            Type::intersection(arguments.argument_types.iter().map(value_type)),
            UntypedOrigin::Propagated,
        ),
        "noreturn" => (Type::Never, UntypedOrigin::Propagated),
        "absurd" => {
            if !actual.is_never() {
                analyzer.error_at(
                    input.site,
                    format!("Expected `T.noreturn`, but found `{actual}`"),
                );
            }
            (Type::Never, UntypedOrigin::Propagated)
        }
        "class_of" => (
            Type::Named("Class".to_owned(), vec![value_type(&actual)]),
            UntypedOrigin::Propagated,
        ),
        "attached_class" => (Type::AttachedClass, UntypedOrigin::Propagated),
        _ => return None,
    };
    Some(result)
}
