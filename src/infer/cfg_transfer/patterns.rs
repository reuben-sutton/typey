//! Owned CFG pattern reachability and value narrowing.

use super::super::cfg_state::BlockState;
use super::super::{ivar_refinement_key, Analyzer};
use crate::cfg;
use crate::hir::{self, ExprKind, Literal, Read};
use crate::types::Type;

#[derive(Clone, Copy, Debug)]
pub(super) struct PatternSource {
    pub(super) expression: hir::ExprId,
    pub(super) truthy: bool,
}

pub(super) fn narrow_pattern_value(
    analyzer: &mut Analyzer<'_>,
    state: &mut BlockState,
    value: cfg::ValueId,
    pattern: &cfg::Pattern,
    truthy: bool,
    source_place: Option<&cfg::Place>,
    source: Option<PatternSource>,
) {
    let Some(source_type) = state.value(value) else {
        return;
    };
    let pattern_source_place = match pattern {
        cfg::Pattern::Case { source_place, .. } => source_place.as_ref(),
        _ => source_place,
    };
    let open_local = matches!(
        pattern_source_place,
        Some(cfg::Place::Local(local))
            if analyzer
                .program
                .hir_program
                .local_name(*local)
                .is_some_and(|name| state.environment.is_open(name.as_str()))
    );
    let narrowed = match pattern {
        cfg::Pattern::Nil => {
            if truthy {
                source_type.meet(&Type::Nil)
            } else {
                source_type.without(&Type::Nil)
            }
        }
        cfg::Pattern::Truthy | cfg::Pattern::LogicalAnd | cfg::Pattern::LogicalOr => {
            if open_local {
                // The observed type is not exhaustive for an open method
                // parameter.  Keep the branch reachable, but widen the
                // branch-local value before checking operations on it.
                Type::Any
            } else if truthy {
                source_type.truthy_part()
            } else {
                source_type.falsy_part()
            }
        }
        cfg::Pattern::Iteration => source_type,
        cfg::Pattern::Case {
            condition,
            expression,
            ..
        } => {
            let condition = state.value(*condition).unwrap_or(Type::Any);
            if !case_pattern_is_type_test(analyzer, *expression, &condition) {
                source_type
            } else {
                let expected = Analyzer::class_object_value_type(&condition).unwrap_or(condition);
                if truthy {
                    analyzer.meet_predicate_type(&source_type, &expected)
                } else {
                    source_type.without(&expected)
                }
            }
        }
    };
    let discriminated = truthy.then(|| discriminated_case_type(analyzer, state, pattern));
    let narrowed = discriminated
        .as_ref()
        .and_then(Option::as_ref)
        .cloned()
        .unwrap_or(narrowed);
    state.set_value(value, narrowed.clone());
    if let Some(source_place) = pattern_source_place {
        let is_discriminator = case_has_type_discriminator(analyzer, pattern);
        if !is_discriminator || discriminated.as_ref().is_some_and(Option::is_some) {
            match source_place {
                cfg::Place::Local(local) => {
                    if let Some(name) = analyzer.program.hir_program.local_name(*local) {
                        state
                            .environment
                            .bind(name.as_str().to_owned(), narrowed.clone());
                    }
                }
                cfg::Place::InstanceVariable(name) => {
                    state
                        .environment
                        .bind(ivar_refinement_key(name.as_str()), narrowed.clone());
                }
                _ => {}
            }
        }
    }
    if matches!(
        pattern,
        cfg::Pattern::Truthy | cfg::Pattern::LogicalAnd | cfg::Pattern::LogicalOr
    ) {
        let Some(source) = source else {
            return;
        };
        analyzer.narrow_cfg_predicate(
            source.expression,
            &mut state.environment,
            truthy == source.truthy,
        );
    }
}

fn case_has_type_discriminator(analyzer: &Analyzer<'_>, pattern: &cfg::Pattern) -> bool {
    let cfg::Pattern::Case {
        discriminator: Some(discriminator),
        ..
    } = pattern
    else {
        return false;
    };
    matches!(
        analyzer
            .program
            .hir_program
            .expression(*discriminator)
            .map(|expression| &expression.kind),
        Some(hir::ExprKind::Call(call)) if call.name.as_str() == "type"
    )
}

fn discriminated_case_type(
    analyzer: &Analyzer<'_>,
    state: &BlockState,
    pattern: &cfg::Pattern,
) -> Option<Type> {
    let cfg::Pattern::Case {
        expression,
        discriminator: Some(discriminator),
        ..
    } = pattern
    else {
        return None;
    };
    let Some(hir::ExprKind::Call(call)) = analyzer
        .program
        .hir_program
        .expression(*discriminator)
        .map(|expression| &expression.kind)
    else {
        return None;
    };
    if call.name.as_str() != "type" {
        return None;
    }
    let hir::Receiver::Explicit(receiver) = &call.receiver else {
        return None;
    };
    let Some(hir::ExprKind::Read(Read::Local(local))) = analyzer
        .program
        .hir_program
        .expression(*receiver)
        .map(|expression| &expression.kind)
    else {
        return None;
    };
    let local_name = analyzer
        .program
        .hir_program
        .local_name(*local)
        .map(|name| name.as_str().to_owned())?;
    let current = state.environment.get(&local_name);
    let current_name = Analyzer::named_type_name(&current)?;
    let Some(hir::ExprKind::Literal(Literal::Symbol(symbol))) = analyzer
        .program
        .hir_program
        .expression(*expression)
        .map(|expression| &expression.kind)
    else {
        return None;
    };
    let narrowed = analyzer
        .fixpoint
        .symbol_method_returns
        .iter()
        .filter_map(|(key, method_symbol)| {
            (key.name == "type"
                && !key.singleton
                && method_symbol == symbol
                && key
                    .owner
                    .as_deref()
                    .is_some_and(|owner| analyzer.nominal_subtype(owner, &current_name)))
            .then(|| Type::named(key.owner.as_ref().expect("owner checked").clone()))
        })
        .collect::<Vec<_>>();
    (!narrowed.is_empty()).then(|| Type::union(narrowed))
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

pub(super) fn pattern_source(graph: &cfg::Cfg, value: cfg::ValueId) -> Option<PatternSource> {
    let operation = graph.blocks.iter().find_map(|block| {
        block
            .operations
            .iter()
            .find(|operation| operation.result == Some(value))
    })?;
    let expression = operation.expression?;
    match &operation.kind {
        cfg::OperationKind::Read { .. } => Some(PatternSource {
            expression,
            truthy: true,
        }),
        cfg::OperationKind::Call {
            receiver: cfg::ReceiverOperand::Value(receiver),
            name,
            ..
        } if name.as_str() == "!" => {
            let mut source = pattern_source(graph, *receiver)?;
            source.truthy = !source.truthy;
            Some(source)
        }
        _ => None,
    }
}

pub(super) fn branch_pattern_source(
    graph: &cfg::Cfg,
    condition: cfg::ValueId,
) -> Option<PatternSource> {
    let operation = graph.blocks.iter().find_map(|block| {
        block
            .operations
            .iter()
            .find(|operation| operation.result == Some(condition))
    })?;
    matches!(
        operation.kind,
        cfg::OperationKind::PatternTest {
            pattern: cfg::Pattern::Truthy,
            ..
        }
    )
    .then(|| {
        operation.expression.map(|expression| PatternSource {
            expression,
            truthy: true,
        })
    })
    .flatten()
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
        ExprKind::Read(Read::Constant(path)) => {
            let name = path.as_str().trim_start_matches("::");
            // A namespaced constant ending in a built-in class name is not
            // necessarily a class object. For example,
            // `Definition::Kind::Class` is an enum value, not a `Class` case
            // test. Treat it as a type test only when the complete constant
            // names a declared class, or when it is one of Ruby's top-level
            // built-in class constants.
            analyzer.declarations.classes.contains_key(name)
                || matches!(
                    name,
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
        }
        // Other literals and constant values are ordinary `===` patterns,
        // not class tests. Their runtime value may match only some instances
        // of the source type, so their branch must remain reachable.
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
            ..
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

pub(super) fn case_match_reachability(
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
        // An arbitrary case pattern can override `===` and a value such as a
        // Regexp can match only part of a nominal source type. Without an
        // owned proof of the pattern's runtime matcher, retain both paths.
        return (true, true);
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
