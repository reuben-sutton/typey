//! Owned CFG branch reachability and predicate refinement.

use super::super::cfg_state::BlockState;
use super::super::{Analyzer, Environment};
use super::patterns::truthiness_reachability;
use crate::cfg;
use crate::hir::{self, Read};
use crate::types::Type;

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
    analyzer: &Analyzer<'_>,
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
        if let Some(truthy) = state.environment.known_truthiness(name.as_str()) {
            return (truthy, !truthy);
        }
        if state.environment.is_inferred(name.as_str()) {
            return (true, true);
        }
    }
    if let Some(hir::ExprKind::Call(call)) = condition
        .and_then(|condition| analyzer.program.hir_program.expression(condition))
        .map(|expression| &expression.kind)
    {
        if call.name.as_str() == "!" {
            if let hir::Receiver::Explicit(receiver) = call.receiver {
                if let Some(hir::ExprKind::Read(Read::Local(local))) = analyzer
                    .program
                    .hir_program
                    .expression(receiver)
                    .map(|expression| &expression.kind)
                {
                    if let Some(name) = analyzer.program.hir_program.local_name(*local) {
                        if let Some(truthy) = state.environment.known_truthiness(name.as_str()) {
                            return (!truthy, truthy);
                        }
                        if state.environment.is_inferred(name.as_str()) {
                            return (true, true);
                        }
                    }
                }
                let receiver_value = graph.value_for(receiver);
                if let Some(receiver_value) = receiver_value {
                    let receiver_type = state.value(receiver_value);
                    if let Some(receiver_type) = receiver_type {
                        // Unary negation publishes the ordinary boolean
                        // result, but its operand can still prove the
                        // branch's truth value (for example `if
                        // !nil.blank?`). Keep that proof at the branch
                        // boundary rather than widening the source call away
                        // from `T::Boolean`.
                        return (
                            !receiver_type.falsy_part().is_never(),
                            !receiver_type.truthy_part().is_never(),
                        );
                    }
                }
            }
        }
    }
    truthiness_reachability(source)
}
