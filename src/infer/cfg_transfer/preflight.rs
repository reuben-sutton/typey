//! HIR-only capability checks for the owned CFG transfer path.
//!
//! This layer deliberately has no analyzer state and no Prism dependency. It
//! answers only whether a body can be represented by the current owned CFG
//! contract; it does not infer a type or decide whether a program is valid.

use crate::hir::{self, ArrayElement, ExprKind, HashElement};
use std::collections::HashSet;

#[derive(Clone, Copy)]
struct ControlContext {
    allow_return: bool,
    allow_block_outcomes: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PreflightFailure {
    pub(super) span: hir::Span,
    pub(super) reason: String,
}

fn failure(
    program: &hir::Program,
    expression: hir::ExprId,
    reason: &'static str,
) -> PreflightFailure {
    let span = program.expression(expression).map_or_else(
        || hir::Span::new(hir::FileId(0), 0, 0),
        |expression| expression.span,
    );
    PreflightFailure {
        span,
        reason: reason.to_owned(),
    }
}

pub(super) fn body_transfer_failure(
    program: &hir::Program,
    body_id: hir::BodyId,
) -> Option<PreflightFailure> {
    let body = program.body(body_id)?;
    let mut visiting = HashSet::new();
    let context = ControlContext {
        allow_return: body_allows_return(program, body),
        allow_block_outcomes: matches!(
            &body.owner,
            hir::BodyOwner::Closure(closure_id)
                if program
                    .closure(*closure_id)
                    .is_some_and(|closure| closure.kind == hir::ClosureKind::Block)
        ),
    };
    expr_transfer_failure(program, body.root, &mut visiting, 0, context).err()
}

fn body_allows_return(program: &hir::Program, body: &hir::Body) -> bool {
    match &body.owner {
        hir::BodyOwner::Method { .. } => true,
        hir::BodyOwner::TopLevel => false,
        hir::BodyOwner::Closure(closure_id) => program.closure(*closure_id).is_some(),
        hir::BodyOwner::Class(_) | hir::BodyOwner::Module(_) | hir::BodyOwner::SingletonClass => {
            false
        }
    }
}

fn expr_transfer_failure(
    program: &hir::Program,
    expression: hir::ExprId,
    visiting: &mut HashSet<hir::ExprId>,
    loop_depth: usize,
    context: ControlContext,
) -> Result<(), PreflightFailure> {
    if !visiting.insert(expression) {
        return Err(failure(program, expression, "cyclic HIR expression"));
    }
    let Some(expr) = program.expression(expression) else {
        visiting.remove(&expression);
        return Err(failure(program, expression, "missing HIR expression"));
    };
    let result = match &expr.kind {
        ExprKind::Nil | ExprKind::Literal(_) | ExprKind::Read(_) => Ok(()),
        ExprKind::Defined { value } => {
            expr_transfer_failure(program, *value, visiting, loop_depth, context)
        }
        ExprKind::Call(call) => {
            if let Some(block) = &call.block {
                match block {
                    hir::BlockArgument::Inline(closure) => {
                        let Some(closure) = program.closure(*closure) else {
                            return Err(failure(program, expression, "missing inline closure"));
                        };
                        if let Some(failure) = body_transfer_failure(program, closure.body) {
                            return Err(failure);
                        }
                    }
                    hir::BlockArgument::Passed(value) => {
                        expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
                    }
                }
            }
            if let hir::Receiver::Explicit(receiver) = &call.receiver {
                expr_transfer_failure(program, *receiver, visiting, loop_depth, context)?;
            }
            for argument in &call.arguments {
                match argument {
                    hir::Argument::Positional(value)
                    | hir::Argument::Splat(value)
                    | hir::Argument::Keyword { value, .. }
                    | hir::Argument::KeywordSplat(value) => {
                        expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
                    }
                    hir::Argument::Forwarded => {}
                }
            }
            Ok(())
        }
        ExprKind::Array(elements) => {
            for element in elements {
                let value = match element {
                    ArrayElement::Value(value) | ArrayElement::Splat { value, .. } => value,
                };
                expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Hash(elements) => {
            for element in elements {
                match element {
                    HashElement::Pair { key, value } => {
                        expr_transfer_failure(program, *key, visiting, loop_depth, context)?;
                        expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
                    }
                    HashElement::Splat { value, .. } => {
                        expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
                    }
                }
            }
            Ok(())
        }
        ExprKind::Interpolated { parts, .. } => {
            for part in parts {
                expr_transfer_failure(program, *part, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Range { left, right, .. } => {
            if let Some(left) = left {
                expr_transfer_failure(program, *left, visiting, loop_depth, context)?;
            }
            if let Some(right) = right {
                expr_transfer_failure(program, *right, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Logical { left, right, .. } => {
            expr_transfer_failure(program, *left, visiting, loop_depth, context)?;
            expr_transfer_failure(program, *right, visiting, loop_depth, context)
        }
        ExprKind::Closure(closure) => {
            let Some(closure) = program.closure(*closure) else {
                return Err(failure(program, expression, "missing closure"));
            };
            if let Some(failure) = body_transfer_failure(program, closure.body) {
                Err(failure)
            } else {
                Ok(())
            }
        }
        ExprKind::Begin(begin) => {
            if let Some(body) = begin.body {
                expr_transfer_failure(program, body, visiting, loop_depth, context)?;
            }
            if let Some(body) = begin.else_body {
                expr_transfer_failure(program, body, visiting, loop_depth, context)?;
            }
            for clause in &begin.rescue {
                for exception in &clause.exceptions {
                    expr_transfer_failure(program, *exception, visiting, loop_depth, context)?;
                }
                if let Some(body) = clause.body {
                    expr_transfer_failure(program, body, visiting, loop_depth, context)?;
                }
            }
            if let Some(ensure) = begin.ensure {
                expr_transfer_failure(program, ensure, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Assign { target, value, .. } => {
            match target {
                hir::AssignTarget::Local(_)
                | hir::AssignTarget::InstanceVariable(_)
                | hir::AssignTarget::ClassVariable(_)
                | hir::AssignTarget::Global(_)
                | hir::AssignTarget::Constant(_) => {}
                hir::AssignTarget::Attribute { receiver, .. } => {
                    expr_transfer_failure(program, *receiver, visiting, loop_depth, context)?;
                }
                hir::AssignTarget::Index {
                    receiver,
                    arguments,
                } => {
                    expr_transfer_failure(program, *receiver, visiting, loop_depth, context)?;
                    for argument in arguments {
                        match argument {
                            hir::Argument::Forwarded => {
                                return Err(failure(
                                    program,
                                    expression,
                                    "forwarded index-assignment operand",
                                ));
                            }
                            hir::Argument::Positional(value)
                            | hir::Argument::Splat(value)
                            | hir::Argument::Keyword { value, .. }
                            | hir::Argument::KeywordSplat(value) => {
                                expr_transfer_failure(
                                    program, *value, visiting, loop_depth, context,
                                )?;
                            }
                        }
                    }
                }
            }
            expr_transfer_failure(program, *value, visiting, loop_depth, context)
        }
        ExprKind::MultiAssign {
            lefts,
            rest,
            rights,
            value,
        } => {
            if lefts
                .iter()
                .chain(rest.iter())
                .chain(rights.iter())
                .any(|target| {
                    matches!(
                        target,
                        hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. }
                    )
                })
            {
                return Err(failure(
                    program,
                    expression,
                    "multi-assignment target requires a setter call",
                ));
            }
            expr_transfer_failure(program, *value, visiting, loop_depth, context)
        }
        ExprKind::Sequence(expressions) => {
            for expression in expressions {
                expr_transfer_failure(program, *expression, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Retry => Ok(()),
        ExprKind::Loop(loop_expr) => {
            match loop_expr.kind {
                hir::LoopKind::For => {
                    if !loop_expr.index.as_ref().is_some_and(|target| {
                        matches!(
                            target,
                            hir::AssignTarget::Local(_)
                                | hir::AssignTarget::InstanceVariable(_)
                                | hir::AssignTarget::ClassVariable(_)
                                | hir::AssignTarget::Global(_)
                                | hir::AssignTarget::Constant(_)
                        )
                    }) {
                        return Err(failure(program, expression, "unsupported for-loop target"));
                    }
                }
                hir::LoopKind::While | hir::LoopKind::Until => {
                    if loop_expr.index.is_some() {
                        return Err(failure(
                            program,
                            expression,
                            "while/until loop has an assignment target",
                        ));
                    }
                }
            }
            expr_transfer_failure(program, loop_expr.condition, visiting, loop_depth, context)?;
            if let Some(body) = loop_expr.body {
                expr_transfer_failure(program, body, visiting, loop_depth + 1, context)?;
            }
            Ok(())
        }
        ExprKind::Case(case) => {
            if let Some(scrutinee) = case.scrutinee {
                expr_transfer_failure(program, scrutinee, visiting, loop_depth, context)?;
            }
            for arm in &case.arms {
                for condition in &arm.conditions {
                    expr_transfer_failure(program, *condition, visiting, loop_depth, context)?;
                }
                expr_transfer_failure(program, arm.body, visiting, loop_depth, context)?;
            }
            if let Some(else_body) = case.else_body {
                expr_transfer_failure(program, else_body, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Return(value) => {
            if !context.allow_return {
                return Err(failure(
                    program,
                    expression,
                    "return is not valid in this body",
                ));
            }
            if let Some(value) = value {
                expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Break(value) | ExprKind::Next(value) => {
            if loop_depth == 0 && !context.allow_block_outcomes {
                return Err(failure(
                    program,
                    expression,
                    "break/next is not valid outside a loop or block",
                ));
            }
            if let Some(value) = value {
                expr_transfer_failure(program, *value, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_transfer_failure(program, *condition, visiting, loop_depth, context)?;
            expr_transfer_failure(program, *then_body, visiting, loop_depth, context)?;
            if let Some(else_body) = else_body {
                expr_transfer_failure(program, *else_body, visiting, loop_depth, context)?;
            }
            Ok(())
        }
        ExprKind::Definition(_) => Err(failure(
            program,
            expression,
            "declaration expression is handled outside owned body transfer",
        )),
        ExprKind::Unsupported(unsupported) => {
            let span = expr.span;
            Err(PreflightFailure {
                span,
                reason: format!(
                    "unsupported HIR parent `{}` is not represented by owned CFG transfer",
                    unsupported.kind.as_str()
                ),
            })
        }
    };
    visiting.remove(&expression);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_the_owned_span_and_reason_for_unsupported_hir() {
        let program = hir::lower(hir::FileId(3), b"alias foo bar");
        let body = program.root.expect("root body");
        let failure = body_transfer_failure(&program, body).expect("unsupported expression");
        let expression = program.body(body).expect("body").root;

        assert_eq!(failure.span, program.expression(expression).unwrap().span);
        assert!(failure.reason.contains("unsupported HIR parent"));
    }

    #[test]
    fn supported_owned_expression_has_no_preflight_failure() {
        let program = hir::lower(hir::FileId(3), b"1 + 2");
        let body = program.root.expect("root body");

        assert_eq!(body_transfer_failure(&program, body), None);
    }
}
