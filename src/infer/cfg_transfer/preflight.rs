//! HIR-only capability checks for the owned CFG transfer path.
//!
//! This layer deliberately has no analyzer state and no Prism dependency. It
//! answers only whether a body can be represented by the current owned CFG
//! contract; it does not infer a type or decide whether a program is valid.

use super::*;

pub(super) fn body_can_transfer(program: &hir::Program, body: hir::BodyId) -> bool {
    let Some(body) = program.body(body) else {
        return false;
    };
    let mut visiting = HashSet::new();
    expr_can_transfer(
        program,
        body.root,
        &mut visiting,
        0,
        body_allows_local_return(program, body),
    )
}

fn body_allows_local_return(program: &hir::Program, body: &hir::Body) -> bool {
    match &body.owner {
        hir::BodyOwner::Method { .. } => true,
        hir::BodyOwner::TopLevel => false,
        hir::BodyOwner::Closure(closure_id) => program
            .closure(*closure_id)
            .is_some_and(|closure| closure.kind == hir::ClosureKind::Lambda),
        hir::BodyOwner::Class(_) | hir::BodyOwner::Module(_) | hir::BodyOwner::SingletonClass => {
            false
        }
    }
}

fn expr_can_transfer(
    program: &hir::Program,
    expression: hir::ExprId,
    visiting: &mut HashSet<hir::ExprId>,
    loop_depth: usize,
    local_return: bool,
) -> bool {
    if !visiting.insert(expression) {
        return false;
    }
    let Some(expr) = program.expression(expression) else {
        return false;
    };
    let supported = match &expr.kind {
        ExprKind::Nil | ExprKind::Literal(_) | ExprKind::Read(_) => true,
        ExprKind::Call(call) => {
            let block_supported = call.block.as_ref().is_none_or(|block| match block {
                hir::BlockArgument::Inline(closure) => {
                    !matches!(
                        call.name.as_str(),
                        "define_method" | "define_singleton_method"
                    ) && program
                        .closure(*closure)
                        .is_some_and(|closure| body_can_transfer(program, closure.body))
                }
                hir::BlockArgument::Passed(value) => {
                    expr_can_transfer(program, *value, visiting, loop_depth, local_return)
                }
            });
            block_supported
                && match &call.receiver {
                    hir::Receiver::Implicit
                    | hir::Receiver::Explicit(_)
                    | hir::Receiver::Super
                    | hir::Receiver::Yield => true,
                }
                && match &call.receiver {
                    hir::Receiver::Explicit(receiver) => {
                        expr_can_transfer(program, *receiver, visiting, loop_depth, local_return)
                    }
                    _ => true,
                }
                && call.arguments.iter().all(|argument| match argument {
                    hir::Argument::Positional(value) | hir::Argument::Splat(value) => {
                        expr_can_transfer(program, *value, visiting, loop_depth, local_return)
                    }
                    hir::Argument::Keyword { value, .. } => {
                        expr_can_transfer(program, *value, visiting, loop_depth, local_return)
                    }
                    hir::Argument::KeywordSplat(value) => {
                        expr_can_transfer(program, *value, visiting, loop_depth, local_return)
                    }
                    hir::Argument::Forwarded => true,
                })
        }
        ExprKind::Array(elements) => elements.iter().all(|element| match element {
            ArrayElement::Value(value) => {
                expr_can_transfer(program, *value, visiting, loop_depth, local_return)
            }
            ArrayElement::Splat { value, .. } => {
                expr_can_transfer(program, *value, visiting, loop_depth, local_return)
            }
        }),
        ExprKind::Hash(elements) => elements.iter().all(|element| match element {
            HashElement::Pair { key, value } => {
                expr_can_transfer(program, *key, visiting, loop_depth, local_return)
                    && expr_can_transfer(program, *value, visiting, loop_depth, local_return)
            }
            HashElement::Splat { value, .. } => {
                expr_can_transfer(program, *value, visiting, loop_depth, local_return)
            }
        }),
        ExprKind::Closure(closure) => program
            .closure(*closure)
            .is_some_and(|closure| body_can_transfer(program, closure.body)),
        ExprKind::Begin(begin) => {
            begin.body.is_none_or(|body| {
                expr_can_transfer(program, body, visiting, loop_depth, local_return)
            }) && begin.else_body.is_none_or(|body| {
                expr_can_transfer(program, body, visiting, loop_depth, local_return)
            }) && begin.rescue.iter().all(|clause| {
                clause.exceptions.iter().all(|exception| {
                    expr_can_transfer(program, *exception, visiting, loop_depth, local_return)
                }) && clause.body.is_none_or(|body| {
                    expr_can_transfer(program, body, visiting, loop_depth, local_return)
                })
            }) && begin.ensure.is_none_or(|ensure| {
                expr_can_transfer(program, ensure, visiting, loop_depth, local_return)
            })
        }
        ExprKind::Assign { target, value, .. } => {
            let target_supported = match target {
                hir::AssignTarget::Local(_)
                | hir::AssignTarget::InstanceVariable(_)
                | hir::AssignTarget::ClassVariable(_)
                | hir::AssignTarget::Global(_)
                | hir::AssignTarget::Constant(_) => true,
                hir::AssignTarget::Attribute { receiver, .. } => {
                    expr_can_transfer(program, *receiver, visiting, loop_depth, local_return)
                }
                hir::AssignTarget::Index {
                    receiver,
                    arguments,
                } => {
                    expr_can_transfer(program, *receiver, visiting, loop_depth, local_return)
                        && arguments.iter().all(|argument| match argument {
                            hir::Argument::Positional(value) => expr_can_transfer(
                                program,
                                *value,
                                visiting,
                                loop_depth,
                                local_return,
                            ),
                            hir::Argument::Splat(_)
                            | hir::Argument::Keyword { .. }
                            | hir::Argument::KeywordSplat(_)
                            | hir::Argument::Forwarded => false,
                        })
                }
            };
            target_supported
                && expr_can_transfer(program, *value, visiting, loop_depth, local_return)
        }
        ExprKind::Sequence(expressions) => expressions.iter().all(|expression| {
            expr_can_transfer(program, *expression, visiting, loop_depth, local_return)
        }),
        ExprKind::Retry => true,
        ExprKind::Loop(loop_expr) => {
            let target_supported = match loop_expr.kind {
                hir::LoopKind::For => loop_expr.index.as_ref().is_some_and(|target| {
                    matches!(
                        target,
                        hir::AssignTarget::Local(_)
                            | hir::AssignTarget::InstanceVariable(_)
                            | hir::AssignTarget::ClassVariable(_)
                            | hir::AssignTarget::Global(_)
                            | hir::AssignTarget::Constant(_)
                    )
                }),
                hir::LoopKind::While | hir::LoopKind::Until => loop_expr.index.is_none(),
            };
            target_supported
                && expr_can_transfer(
                    program,
                    loop_expr.condition,
                    visiting,
                    loop_depth,
                    local_return,
                )
                && loop_expr.body.is_none_or(|body| {
                    expr_can_transfer(program, body, visiting, loop_depth + 1, local_return)
                })
        }
        ExprKind::Case(case) => {
            case.scrutinee.is_none_or(|scrutinee| {
                expr_can_transfer(program, scrutinee, visiting, loop_depth, local_return)
            }) && case.arms.iter().all(|arm| {
                arm.conditions.iter().all(|condition| {
                    expr_can_transfer(program, *condition, visiting, loop_depth, local_return)
                }) && expr_can_transfer(program, arm.body, visiting, loop_depth, local_return)
            }) && case.else_body.is_none_or(|else_body| {
                expr_can_transfer(program, else_body, visiting, loop_depth, local_return)
            })
        }
        ExprKind::Return(value) => {
            local_return
                && value.is_none_or(|value| {
                    expr_can_transfer(program, value, visiting, loop_depth, local_return)
                })
        }
        ExprKind::Break(value) | ExprKind::Next(value) => {
            loop_depth > 0
                && value.is_none_or(|value| {
                    expr_can_transfer(program, value, visiting, loop_depth, local_return)
                })
        }
        ExprKind::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_can_transfer(program, *condition, visiting, loop_depth, local_return)
                && expr_can_transfer(program, *then_body, visiting, loop_depth, local_return)
                && else_body.is_none_or(|else_body| {
                    expr_can_transfer(program, else_body, visiting, loop_depth, local_return)
                })
        }
        _ => false,
    };
    visiting.remove(&expression);
    supported
}
