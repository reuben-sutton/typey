//! Owned CFG branch reachability and predicate refinement.

use super::super::cfg_state::BlockState;
use super::super::{Analyzer, Environment};
use super::patterns::{case_match_reachability, truthiness_reachability};
use crate::cfg;
use crate::hir::{self, Read};
use crate::types::Type;

fn contains_class_object(type_: &Type) -> bool {
    match type_ {
        Type::Union(members) => members.iter().any(contains_class_object),
        type_ => Analyzer::class_object_instance_type(type_).is_some(),
    }
}

pub(super) fn narrow_conditional_branch(
    analyzer: &mut Analyzer<'_>,
    graph: &cfg::Cfg,
    block: cfg::BlockId,
    truthy: bool,
    environment: &mut Environment,
) {
    let Some(conditional) = graph.conditionals.iter().find(|conditional| {
        (truthy && conditional.truthy == block) || (!truthy && conditional.falsy == block)
    }) else {
        return;
    };
    analyzer.narrow_cfg_predicate(conditional.condition, environment, truthy);
}

pub(super) fn conditional_reachability(
    analyzer: &mut Analyzer<'_>,
    graph: &cfg::Cfg,
    truthy: cfg::BlockId,
    falsy: cfg::BlockId,
    source: &Type,
    state: &BlockState,
) -> (bool, bool) {
    let conditional = graph
        .conditionals
        .iter()
        .find(|conditional| conditional.truthy == truthy && conditional.falsy == falsy)
        .cloned();
    let condition = conditional
        .as_ref()
        .map(|conditional| conditional.condition);
    if conditional.is_some_and(|conditional| conditional.loop_condition)
        && !source.truthy_part().is_never()
    {
        // Ruby's while/until expression type includes nil for the path where
        // the loop does not produce a break value. Keep that path alive when
        // a truthy condition would otherwise prune the normal loop exit.
        return (true, true);
    }
    if let Some(hir::ExprKind::Read(Read::Local(local))) = condition
        .and_then(|condition| analyzer.program.hir_program.expression(condition))
        .map(|expression| &expression.kind)
    {
        let Some(name) = analyzer.program.hir_program.local_name(*local) else {
            return truthiness_reachability(source);
        };
        if state.environment.is_inferred(name.as_str()) {
            return (true, true);
        }
    }
    if let Some(condition) = condition {
        if let Some(hir::ExprKind::Call(call)) = analyzer
            .program
            .hir_program
            .expression(condition)
            .map(|expression| expression.kind.clone())
        {
            if matches!(call.name.as_str(), "is_a?" | "kind_of?" | "instance_of?") {
                if let hir::Receiver::Explicit(receiver) = call.receiver {
                    let Some(hir::ExprKind::Read(Read::Local(local))) = analyzer
                        .program
                        .hir_program
                        .expression(receiver)
                        .map(|expression| &expression.kind)
                    else {
                        return truthiness_reachability(source);
                    };
                    let Some(hir::Argument::Positional(argument)) = call.arguments.first() else {
                        return truthiness_reachability(source);
                    };
                    let Some(name) = analyzer
                        .program
                        .hir_program
                        .local_name(*local)
                        .map(|name| name.as_str().to_owned())
                    else {
                        return truthiness_reachability(source);
                    };
                    let current = state.environment.get(&name);
                    let expected =
                        analyzer.cfg_predicate_argument_type(*argument, &state.environment);
                    if contains_class_object(&current) {
                        // A class object is an instance of Class/Module, not
                        // an instance of the class represented by its type
                        // argument. The nominal instance disjointness rule
                        // must not make reflective calls such as
                        // `base.is_a?(Module)` unreachable.
                        return truthiness_reachability(source);
                    }
                    return case_match_reachability(analyzer, &current, &expected, true);
                }
            }
        }
    }
    truthiness_reachability(source)
}
