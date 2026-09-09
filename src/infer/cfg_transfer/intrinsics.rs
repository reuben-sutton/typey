//! Parser-free Sorbet intrinsic contracts for owned CFG calls.

use super::super::{Analyzer, CallArguments, OwnedCallInput, UntypedOrigin};
use crate::types::Type;

pub(super) fn transfer_intrinsic_call(
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
) -> Option<(Type, UntypedOrigin)> {
    let is_t = match receiver {
        Type::Named(name, _) | Type::TypeVar(name) => name == "T",
        _ => false,
    };
    if !is_t {
        return None;
    }
    let actual = arguments
        .argument_types
        .first()
        .cloned()
        .unwrap_or(Type::Any);
    let result = match input.name.as_str() {
        "must" => (actual.without(&Type::Nil), UntypedOrigin::Propagated),
        "unsafe" => (Type::Any, UntypedOrigin::Unsafe),
        "cast" => {
            let expected = arguments
                .argument_types
                .get(1)
                .map(|type_| {
                    Analyzer::class_object_value_type(type_).unwrap_or_else(|| type_.clone())
                })
                .unwrap_or(Type::Any);
            (expected, UntypedOrigin::Propagated)
        }
        _ => return None,
    };
    Some(result)
}
