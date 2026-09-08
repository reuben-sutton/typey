//! Owned CFG pattern reachability and value narrowing.

use super::super::cfg_state::BlockState;
use super::super::{ivar_refinement_key, Analyzer};
use crate::cfg;
use crate::hir::{self, ExprKind, Literal, Read};
use crate::types::Type;

pub(super) fn narrow_pattern_value(
    analyzer: &Analyzer<'_>,
    state: &mut BlockState,
    value: cfg::ValueId,
    pattern: &cfg::Pattern,
    truthy: bool,
    source_place: Option<&cfg::Place>,
) {
    let Some(source) = state.value(value) else {
        return;
    };
    let narrowed = match pattern {
        cfg::Pattern::Nil => {
            if truthy {
                source.meet(&Type::Nil)
            } else {
                source.without(&Type::Nil)
            }
        }
        cfg::Pattern::Truthy | cfg::Pattern::LogicalAnd | cfg::Pattern::LogicalOr => {
            if truthy {
                source.truthy_part()
            } else {
                source.falsy_part()
            }
        }
        cfg::Pattern::Iteration => source,
        cfg::Pattern::Case {
            condition,
            expression,
        } => {
            let condition = state.value(*condition).unwrap_or(Type::Any);
            if !case_pattern_is_type_test(analyzer, *expression, &condition) {
                source
            } else {
                let expected = Analyzer::class_object_value_type(&condition).unwrap_or(condition);
                if truthy {
                    analyzer.meet_predicate_type(&source, &expected)
                } else {
                    source.without(&expected)
                }
            }
        }
    };
    state.set_value(value, narrowed.clone());
    if let Some(source_place) = source_place {
        match source_place {
            cfg::Place::Local(local) => {
                if let Some(name) = analyzer.program.hir_program.local_name(*local) {
                    state.environment.bind(name.as_str().to_owned(), narrowed);
                }
            }
            cfg::Place::InstanceVariable(name) => {
                state
                    .environment
                    .bind(ivar_refinement_key(name.as_str()), narrowed);
            }
            _ => {}
        }
    }
}

pub(super) fn pattern_source_place(graph: &cfg::Cfg, value: cfg::ValueId) -> Option<cfg::Place> {
    graph.blocks.iter().find_map(|block| {
        block.operations.iter().find_map(|operation| {
            (operation.result == Some(value)).then(|| match &operation.kind {
                cfg::OperationKind::Read { place } => Some(place.clone()),
                _ => None,
            })?
        })
    })
}

pub(super) fn case_pattern_is_type_test(
    analyzer: &Analyzer<'_>,
    expression: hir::ExprId,
    condition: &Type,
) -> bool {
    if Analyzer::class_object_value_type(condition).is_some() {
        return true;
    }
    let Some(expression) = analyzer.program.hir_program.expression(expression) else {
        return false;
    };
    match &expression.kind {
        ExprKind::Literal(Literal::Nil | Literal::True | Literal::False) => true,
        ExprKind::Read(Read::Constant(path)) => matches!(
            path.as_str().rsplit("::").next(),
            Some(
                "Array"
                    | "BasicObject"
                    | "Class"
                    | "Complex"
                    | "FalseClass"
                    | "Float"
                    | "Hash"
                    | "Integer"
                    | "NilClass"
                    | "Numeric"
                    | "Object"
                    | "Rational"
                    | "Regexp"
                    | "String"
                    | "Symbol"
                    | "TrueClass"
            )
        ),
        _ => false,
    }
}

pub(super) fn pattern_reachability(
    analyzer: &Analyzer<'_>,
    pattern: &cfg::Pattern,
    source: &Type,
    state: &BlockState,
) -> Option<(bool, bool, Type)> {
    let (truthy, falsy) = match pattern {
        cfg::Pattern::Truthy | cfg::Pattern::LogicalAnd | cfg::Pattern::LogicalOr => (
            !source.truthy_part().is_never(),
            !source.falsy_part().is_never(),
        ),
        cfg::Pattern::Nil => (
            !source.meet(&Type::Nil).is_never(),
            !source.without(&Type::Nil).is_never(),
        ),
        cfg::Pattern::Iteration => (true, true),
        cfg::Pattern::Case {
            condition: condition_id,
            expression,
        } => {
            let condition = state.value(*condition_id).unwrap_or(Type::Any);
            let is_type_test = case_pattern_is_type_test(analyzer, *expression, &condition);
            let expected = Analyzer::class_object_value_type(&condition).unwrap_or(condition);
            case_match_reachability(analyzer, source, &expected, is_type_test)
        }
    };
    let test_type = match (truthy, falsy) {
        (true, true) => Type::union([Type::True, Type::False]),
        (true, false) => Type::True,
        (false, true) => Type::False,
        (false, false) => Type::Never,
    };
    Some((truthy, falsy, test_type))
}

fn case_match_reachability(
    analyzer: &Analyzer<'_>,
    source: &Type,
    expected: &Type,
    is_type_test: bool,
) -> (bool, bool) {
    if source.is_any() || expected.is_any() {
        return (true, true);
    }
    if let Type::Union(members) = source {
        return members
            .iter()
            .fold((false, false), |(truthy, falsy), member| {
                let (member_truthy, member_falsy) =
                    case_match_reachability(analyzer, member, expected, is_type_test);
                (truthy || member_truthy, falsy || member_falsy)
            });
    }
    if !is_type_test {
        return (
            !analyzer.definitely_disjoint_class_types(source, expected),
            true,
        );
    }
    if analyzer.is_assignable(source, expected) {
        (true, false)
    } else if analyzer.is_assignable(expected, source)
        || !analyzer.definitely_disjoint_class_types(source, expected)
    {
        (true, true)
    } else {
        (false, true)
    }
}

pub(super) fn truthiness_reachability(source: &Type) -> (bool, bool) {
    (
        !source.truthy_part().is_never(),
        !source.falsy_part().is_never(),
    )
}
