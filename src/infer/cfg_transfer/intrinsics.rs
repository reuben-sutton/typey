//! Parser-free Sorbet intrinsic contracts for owned CFG calls.

use super::super::{
    Analyzer, CallArguments, Environment, OwnedCallInput, SourceSite, UntypedOrigin,
};
use crate::hir;
use crate::types::Type;

pub(super) fn transfer_intrinsic_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    environment: &Environment,
) -> Option<(Type, UntypedOrigin)> {
    if let Some(type_object) = type_object_receiver(receiver) {
        if matches!(input.name.as_str(), "params" | "returns" | "void" | "bind") {
            return Some((type_object, UntypedOrigin::Propagated));
        }
        return None;
    }
    let is_t = matches!(receiver, Type::Named(name, _) | Type::TypeVar(name) if name == "T")
        || Analyzer::class_object_instance_type(receiver)
            .is_some_and(|instance| matches!(instance, Type::Named(name, _) if name == "T"));
    if !is_t {
        return None;
    }
    let actual = arguments
        .argument_types
        .first()
        .cloned()
        .unwrap_or(Type::Any);
    let result = match input.name.as_str() {
        "proc" => (Type::named("T::Types::Proc"), UntypedOrigin::Propagated),
        "reveal_type" => {
            let site = intrinsic_argument_site(analyzer, input, 0).unwrap_or(input.site);
            let description = actual.to_string();
            analyzer.note_at(site, format!("Revealed type: `{description}`"));
            let untyped_origin = if actual.is_any() {
                intrinsic_expression_source(analyzer, input)
                    .filter(|source| source.contains("T.untyped"))
                    .map_or(UntypedOrigin::FallbackCall, |_| {
                        UntypedOrigin::ExplicitAnnotation
                    })
            } else {
                UntypedOrigin::Propagated
            };
            (actual, untyped_origin)
        }
        "let" | "cast" | "assert_type!" | "bind" => {
            let expected =
                intrinsic_type_argument(analyzer, input, 1, environment).unwrap_or(Type::Any);
            if matches!(input.name.as_str(), "let" | "assert_type!") {
                let site = intrinsic_argument_site(analyzer, input, 0).unwrap_or(input.site);
                analyzer.check_assignable_at(site, &actual, &expected);
            }
            if input.name.as_str() == "assert_type!" {
                (actual, UntypedOrigin::Propagated)
            } else {
                (expected, UntypedOrigin::Propagated)
            }
        }
        "nilable" | "any" | "all" => {
            let source = intrinsic_expression_source(analyzer, input)?;
            let runtime_type_object = source.contains("T.proc");
            if runtime_type_object {
                let name = match input.name.as_str() {
                    "nilable" | "any" => "T::Types::Union",
                    "all" => "T::Types::Intersection",
                    _ => unreachable!(),
                };
                (Type::named(name), UntypedOrigin::Propagated)
            } else {
                let mut value_types = arguments.argument_types.iter().map(|type_| {
                    Analyzer::class_object_value_type(type_).unwrap_or_else(|| type_.clone())
                });
                let type_ = match input.name.as_str() {
                    "nilable" => value_types
                        .next()
                        .map_or(Type::Any, |type_| Type::union([Type::Nil, type_])),
                    "any" => Type::union(value_types),
                    "all" => Type::intersection(value_types),
                    _ => unreachable!(),
                };
                (type_, UntypedOrigin::Propagated)
            }
        }
        "must" => (actual.without(&Type::Nil), UntypedOrigin::Propagated),
        "unsafe" => (Type::Any, UntypedOrigin::Unsafe),
        _ => return None,
    };
    Some(result)
}

fn type_object_receiver(receiver: &Type) -> Option<Type> {
    match receiver {
        Type::Named(name, _) if name.starts_with("T::Types::") => Some(receiver.clone()),
        _ => None,
    }
}

fn intrinsic_expression_source<'src>(
    analyzer: &'src Analyzer<'src>,
    input: &OwnedCallInput,
) -> Option<&'src str> {
    let expression = analyzer.program.hir_program.expression(input.expression?)?;
    let start = expression.span.start as usize;
    let end = expression.span.end as usize;
    std::str::from_utf8(analyzer.program.source.get(start..end)?).ok()
}

fn intrinsic_argument_site(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    index: usize,
) -> Option<SourceSite> {
    let expression = analyzer.program.hir_program.expression(input.expression?)?;
    let hir::ExprKind::Call(call) = &expression.kind else {
        return None;
    };
    let argument = call
        .arguments
        .iter()
        .filter_map(|argument| match argument {
            hir::Argument::Positional(value) => Some(*value),
            _ => None,
        })
        .nth(index)?;
    let expression = analyzer.program.hir_program.expression(argument)?;
    Some(SourceSite::from_span(expression.span, Some(argument)))
}

fn intrinsic_type_argument(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    index: usize,
    environment: &Environment,
) -> Option<Type> {
    let site = intrinsic_argument_site(analyzer, input, index)?;
    let source = analyzer.program.source.get(site.start..site.end)?;
    let parsed = crate::signature::parse_type(std::str::from_utf8(source).ok()?);
    let owner = analyzer.lexical_owner(environment);
    let parsed = analyzer.resolve_type_names(&parsed, owner.as_deref());
    Some(parsed)
}
