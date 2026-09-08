//! Pure lowering from owned HIR to the owned CFG.
//!
//! This module intentionally knows nothing about inference.  Its only job is
//! to make evaluation order, values, storage access, and control transfers
//! explicit while retaining the source spans supplied by HIR.

use super::{
    ArgumentOperand, ArrayOperand, BasicBlock, BlockId, BlockOperand, BlockParameter, Cfg,
    Conditional, HashOperand, Operation, OperationKind, Pattern, Place, ReceiverOperand,
    Terminator, ValueId,
};
use crate::hir::{
    self, Argument, AssignOperator, AssignTarget, BeginExpr, BodyId, ExprId, ExprKind, LoopExpr,
    LoopKind, Program, Read, Span,
};
use std::collections::HashMap;

/// Build a CFG for one already-lowered HIR body.
#[must_use]
pub fn build(program: &Program, body: BodyId) -> Cfg {
    let expressions_by_span = expression_index(program);
    build_with_index_and_values(program, body, Some(&expressions_by_span), true)
}

/// Build all body CFGs while sharing the HIR span index between bodies.
#[must_use]
pub fn build_all(program: &Program) -> Vec<Cfg> {
    let expressions_by_span = expression_index(program);
    program
        .bodies
        .iter()
        .enumerate()
        .map(|(index, _)| {
            build_with_index_and_values(
                program,
                BodyId(index as u32),
                Some(&expressions_by_span),
                true,
            )
        })
        .collect()
}

/// Build all body-local graphs used by transfer without retaining the
/// program-wide expression-value table. These graphs are immutable after
/// lowering and can be cached for every inference pass.
pub(crate) fn build_all_for_index(program: &Program) -> Vec<Cfg> {
    let expressions_by_span = expression_index(program);
    program
        .bodies
        .iter()
        .enumerate()
        .map(|(index, _)| {
            build_with_index_and_values(
                program,
                BodyId(index as u32),
                Some(&expressions_by_span),
                false,
            )
        })
        .collect()
}

pub(crate) fn expression_index(program: &Program) -> HashMap<(u32, u32), ExprId> {
    program
        .expressions
        .iter()
        .enumerate()
        .map(|(index, expression)| {
            (
                (expression.span.start, expression.span.end),
                ExprId(index as u32),
            )
        })
        .collect()
}

pub(crate) fn build_for_index(program: &Program, body: BodyId) -> Cfg {
    build_with_index_and_values(program, body, None, false)
}

fn build_with_index_and_values(
    program: &Program,
    body: BodyId,
    expressions_by_span: Option<&HashMap<(u32, u32), ExprId>>,
    retain_expression_values: bool,
) -> Cfg {
    Builder::new(program, body, expressions_by_span, retain_expression_values).finish()
}

#[derive(Clone, Copy, Debug)]
struct Flow {
    block: BlockId,
    value: Option<ValueId>,
    reachable: bool,
}

#[derive(Clone, Debug)]
enum TargetRuntime {
    Place(Place),
    Attribute {
        receiver: ValueId,
        name: hir::Name,
    },
    Index {
        receiver: ValueId,
        arguments: Vec<ArgumentOperand>,
    },
}

#[derive(Clone, Copy, Debug)]
struct LoopContext {
    break_target: BlockId,
    next_target: BlockId,
}

#[derive(Clone, Copy, Debug)]
struct RescueContext {
    retry_target: BlockId,
}

struct Builder<'program> {
    program: &'program Program,
    expressions_by_span: Option<&'program HashMap<(u32, u32), ExprId>>,
    cfg: Cfg,
    closed: Vec<bool>,
    next_value: u32,
    loops: Vec<LoopContext>,
    rescues: Vec<RescueContext>,
    retain_expression_values: bool,
    current_expression: Option<ExprId>,
}

impl<'program> Builder<'program> {
    fn new(
        program: &'program Program,
        body: BodyId,
        expressions_by_span: Option<&'program HashMap<(u32, u32), ExprId>>,
        retain_expression_values: bool,
    ) -> Self {
        Self {
            program,
            expressions_by_span,
            cfg: Cfg {
                body,
                entry: BlockId(0),
                blocks: Vec::new(),
                conditionals: Vec::new(),
                ensure_entries: Vec::new(),
                unsupported_spans: Vec::new(),
                expression_values: retain_expression_values
                    .then(|| vec![None; program.expressions.len()])
                    .unwrap_or_default(),
            },
            closed: Vec::new(),
            next_value: 0,
            loops: Vec::new(),
            rescues: Vec::new(),
            retain_expression_values,
            current_expression: None,
        }
    }

    fn finish(mut self) -> Cfg {
        let entry = self.new_block_with_unwind(None);
        self.cfg.entry = entry;
        let body = self
            .program
            .body(self.cfg.body)
            .unwrap_or_else(|| panic!("HIR body {:?} does not exist", self.cfg.body));
        let flow = self.lower_expr(body.root, entry);
        if flow.reachable {
            self.set_terminator(flow.block, Terminator::Return(flow.value));
        }
        for (index, block) in self.cfg.blocks.iter_mut().enumerate() {
            if !self.closed[index] {
                block.terminator = Terminator::Unreachable;
                self.closed[index] = true;
            }
        }
        self.cfg
    }

    fn new_value(&mut self) -> ValueId {
        let value = ValueId(self.next_value);
        self.next_value = self.next_value.saturating_add(1);
        value
    }

    fn new_block_with_unwind(&mut self, unwind: Option<BlockId>) -> BlockId {
        let id = BlockId(self.cfg.blocks.len() as u32);
        self.cfg.blocks.push(BasicBlock {
            id,
            parameters: Vec::new(),
            operations: Vec::new(),
            terminator: Terminator::Unreachable,
            unwind,
        });
        self.closed.push(false);
        id
    }

    fn new_block_like(&mut self, block: BlockId) -> BlockId {
        self.new_block_with_unwind(self.unwind(block))
    }

    fn unwind(&self, block: BlockId) -> Option<BlockId> {
        self.cfg.blocks[block.0 as usize].unwind
    }

    fn add_parameter(&mut self, block: BlockId) -> ValueId {
        let value = self.new_value();
        self.cfg.blocks[block.0 as usize]
            .parameters
            .push(BlockParameter {
                value,
                incoming: Vec::new(),
            });
        value
    }

    fn emit(
        &mut self,
        block: BlockId,
        span: Span,
        kind: OperationKind,
        result: bool,
    ) -> Option<ValueId> {
        let value = result.then(|| self.new_value());
        self.cfg.blocks[block.0 as usize]
            .operations
            .push(Operation {
                span,
                expression: self.current_expression.or_else(|| {
                    self.expressions_by_span.and_then(|expressions_by_span| {
                        expressions_by_span.get(&(span.start, span.end)).copied()
                    })
                }),
                result: value,
                kind,
            });
        value
    }

    fn set_terminator(&mut self, block: BlockId, terminator: Terminator) {
        assert!(!self.closed[block.0 as usize], "block already terminated");
        self.cfg.blocks[block.0 as usize].terminator = terminator;
        self.closed[block.0 as usize] = true;
    }

    fn jump(&mut self, from: BlockId, target: BlockId, arguments: Vec<ValueId>) {
        let parameter_values = self.cfg.blocks[target.0 as usize]
            .parameters
            .iter()
            .map(|parameter| parameter.value)
            .collect::<Vec<_>>();
        assert_eq!(
            parameter_values.len(),
            arguments.len(),
            "jump argument count does not match target parameters"
        );
        self.set_terminator(
            from,
            Terminator::Jump {
                target,
                arguments: arguments.clone(),
            },
        );
        let target_block = &mut self.cfg.blocks[target.0 as usize];
        for (parameter, argument) in target_block
            .parameters
            .iter_mut()
            .zip(arguments.into_iter())
        {
            parameter.incoming.push((from, argument));
        }
    }

    fn branch(&mut self, from: BlockId, condition: ValueId, truthy: BlockId, falsy: BlockId) {
        self.set_terminator(
            from,
            Terminator::Branch {
                condition,
                truthy,
                falsy,
            },
        );
    }

    fn normal(&mut self, expression: ExprId, block: BlockId, value: Option<ValueId>) -> Flow {
        if self.retain_expression_values {
            self.cfg.expression_values[expression.0 as usize] = value;
        }
        Flow {
            block,
            value,
            reachable: true,
        }
    }

    fn abrupt(&mut self, expression: ExprId, block: BlockId) -> Flow {
        if self.retain_expression_values {
            self.cfg.expression_values[expression.0 as usize] = None;
        }
        Flow {
            block,
            value: None,
            reachable: false,
        }
    }

    /// Record an expression value on a terminal return path before restoring
    /// the path's original terminator. Recursive inference records enclosing
    /// expressions even when one branch returns, so the CFG must preserve
    /// that source-site observation without turning the return into a join.
    fn record_terminal_return(&mut self, block: BlockId, expression: ExprId) {
        let terminator = std::mem::replace(
            &mut self.cfg.blocks[block.0 as usize].terminator,
            Terminator::Unreachable,
        );
        let Terminator::Return(value) = terminator else {
            self.cfg.blocks[block.0 as usize].terminator = terminator;
            return;
        };
        self.closed[block.0 as usize] = false;
        self.emit(
            block,
            self.span(expression),
            OperationKind::Record { value },
            false,
        );
        self.set_terminator(block, Terminator::Return(value));
    }

    fn lower_expr(&mut self, expression: ExprId, block: BlockId) -> Flow {
        let expr = self
            .program
            .expression(expression)
            .unwrap_or_else(|| panic!("HIR expression {:?} does not exist", expression));
        let span = expr.span;
        let kind = expr.kind.clone();
        let previous_expression = self.current_expression.replace(expression);
        let flow = match kind {
            ExprKind::Nil => self.lower_literal(expression, block, span, hir::Literal::Nil),
            ExprKind::Literal(literal) => self.lower_literal(expression, block, span, literal),
            ExprKind::Read(read) => self.lower_read(expression, block, span, read),
            ExprKind::Assign {
                target,
                value,
                operator,
                ..
            } => self.lower_assignment(expression, block, span, target, value, operator),
            ExprKind::Call(call) => self.lower_call(expression, block, call),
            ExprKind::Array(elements) => self.lower_array(expression, block, span, elements),
            ExprKind::Hash(elements) => self.lower_hash(expression, block, span, elements),
            ExprKind::Closure(closure) => {
                let value = self.emit(block, span, OperationKind::MakeClosure { closure }, true);
                self.normal(expression, block, value)
            }
            ExprKind::Sequence(expressions) => self.lower_sequence(expression, block, expressions),
            ExprKind::If {
                condition,
                then_body,
                else_body,
            } => self.lower_if(expression, block, condition, then_body, else_body),
            ExprKind::Case(case) => self.lower_case(expression, block, span, case),
            ExprKind::Loop(loop_expr) => self.lower_loop(expression, block, span, loop_expr),
            ExprKind::Begin(begin) => self.lower_begin(expression, block, span, begin),
            ExprKind::Return(value) => self.lower_return(expression, block, value),
            ExprKind::Break(value) => self.lower_break(expression, block, value),
            ExprKind::Next(value) => self.lower_next(expression, block, value),
            ExprKind::Retry => self.lower_retry(expression, block, span),
            ExprKind::Definition(_) => {
                self.cfg.unsupported_spans.push(span);
                let value = self.emit(
                    block,
                    span,
                    OperationKind::Unsupported {
                        kind: hir::Name::new("definition"),
                    },
                    true,
                );
                self.normal(expression, block, value)
            }
            ExprKind::Unsupported(unsupported) => {
                self.cfg.unsupported_spans.push(span);
                let value = self.emit(
                    block,
                    span,
                    OperationKind::Unsupported {
                        kind: unsupported.kind,
                    },
                    true,
                );
                let mut flow = self.normal(expression, block, value);
                for child in unsupported.children {
                    if !flow.reachable {
                        break;
                    }
                    flow = self.lower_expr(child, flow.block);
                }
                flow
            }
        };
        self.current_expression = previous_expression;
        flow
    }

    fn lower_literal(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        literal: hir::Literal,
    ) -> Flow {
        let value = self.emit(block, span, OperationKind::Const { value: literal }, true);
        self.normal(expression, block, value)
    }

    fn lower_read(&mut self, expression: ExprId, block: BlockId, span: Span, read: Read) -> Flow {
        let kind = match read {
            Read::Local(local) => OperationKind::Read {
                place: Place::Local(local),
            },
            Read::InstanceVariable(name) => OperationKind::Read {
                place: Place::InstanceVariable(name),
            },
            Read::ClassVariable(name) => OperationKind::Read {
                place: Place::ClassVariable(name),
            },
            Read::Global(name) => OperationKind::Read {
                place: Place::Global(name),
            },
            Read::Constant(path) => OperationKind::Read {
                place: Place::Constant(path),
            },
            special => OperationKind::ReadSpecial { read: special },
        };
        let value = self.emit(block, span, kind, true);
        self.normal(expression, block, value)
    }

    fn lower_sequence(
        &mut self,
        expression: ExprId,
        block: BlockId,
        expressions: Vec<ExprId>,
    ) -> Flow {
        if expressions.is_empty() {
            return self.lower_literal(expression, block, self.span(expression), hir::Literal::Nil);
        }
        let mut flow = self.lower_expr(expressions[0], block);
        for child in expressions.into_iter().skip(1) {
            if !flow.reachable {
                break;
            }
            flow = self.lower_expr(child, flow.block);
        }
        if flow.reachable {
            self.normal(expression, flow.block, flow.value)
        } else {
            self.abrupt(expression, flow.block)
        }
    }

    fn lower_call(&mut self, expression: ExprId, block: BlockId, call: hir::Call) -> Flow {
        let mut block = block;
        let receiver = match call.receiver {
            hir::Receiver::Implicit => ReceiverOperand::Implicit,
            hir::Receiver::Super => ReceiverOperand::Super,
            hir::Receiver::Yield => ReceiverOperand::Yield,
            hir::Receiver::Explicit(receiver) => {
                let flow = self.lower_expr(receiver, block);
                if !flow.reachable {
                    return self.abrupt(expression, flow.block);
                }
                block = flow.block;
                ReceiverOperand::Value(flow.value.expect("receiver produces a value"))
            }
        };

        let mut arguments = Vec::new();
        for argument in call.arguments {
            let (next_block, lowered) = match self.lower_argument(block, argument) {
                Some(value) => value,
                None => return self.abrupt(expression, block),
            };
            block = next_block;
            arguments.push(lowered);
        }

        let block_operand = match call.block {
            None => None,
            Some(hir::BlockArgument::Inline(closure)) => Some(BlockOperand::Inline(closure)),
            Some(hir::BlockArgument::Passed(value)) => {
                let flow = self.lower_expr(value, block);
                if !flow.reachable {
                    return self.abrupt(expression, flow.block);
                }
                block = flow.block;
                Some(BlockOperand::Passed(
                    flow.value.expect("passed block produces a value"),
                ))
            }
        };

        if !call.safe_navigation {
            let value = self.emit(
                block,
                call.span,
                OperationKind::Call {
                    receiver,
                    name: call.name,
                    arguments,
                    block: block_operand,
                    safe_navigation: false,
                },
                true,
            );
            return self.normal(expression, block, value);
        }

        let receiver_value = match receiver {
            ReceiverOperand::Value(value) => value,
            _ => {
                // Prism only permits safe navigation with an explicit
                // receiver. Keep malformed HIR explicit rather than inventing
                // an implicit receiver semantics.
                let value = self.emit(
                    block,
                    call.span,
                    OperationKind::Unsupported {
                        kind: hir::Name::new("safe-navigation-without-receiver"),
                    },
                    true,
                );
                return self.normal(expression, block, value);
            }
        };
        let nil_block = self.new_block_like(block);
        let call_block = self.new_block_like(block);
        let join = self.new_block_like(block);
        let joined = self.add_parameter(join);
        let is_nil = self.emit(
            block,
            call.span,
            OperationKind::PatternTest {
                value: receiver_value,
                pattern: Pattern::Nil,
            },
            true,
        );
        self.branch(
            block,
            is_nil.expect("pattern test produces a value"),
            nil_block,
            call_block,
        );
        let nil_value = self.emit(
            nil_block,
            call.span,
            OperationKind::Const {
                value: hir::Literal::Nil,
            },
            true,
        );
        self.jump(
            nil_block,
            join,
            vec![nil_value.expect("nil produces a value")],
        );
        let call_value = self.emit(
            call_block,
            call.span,
            OperationKind::Call {
                receiver: ReceiverOperand::Value(receiver_value),
                name: call.name,
                arguments,
                block: block_operand,
                safe_navigation: false,
            },
            true,
        );
        self.jump(
            call_block,
            join,
            vec![call_value.expect("call produces a value")],
        );
        self.normal(expression, join, Some(joined))
    }

    fn lower_argument(
        &mut self,
        block: BlockId,
        argument: Argument,
    ) -> Option<(BlockId, ArgumentOperand)> {
        let operand = match argument {
            Argument::Forwarded => return Some((block, ArgumentOperand::Forwarded)),
            Argument::Positional(value) => {
                let flow = self.lower_expr(value, block);
                if !flow.reachable {
                    return None;
                }
                return Some((
                    flow.block,
                    ArgumentOperand::Positional(flow.value.expect("argument produces a value")),
                ));
            }
            Argument::Splat(value) => {
                let flow = self.lower_expr(value, block);
                if !flow.reachable {
                    return None;
                }
                ArgumentOperand::Splat(flow.value.expect("splat produces a value"))
            }
            Argument::Keyword { name, value } => {
                let flow = self.lower_expr(value, block);
                if !flow.reachable {
                    return None;
                }
                return Some((
                    flow.block,
                    ArgumentOperand::Keyword {
                        name,
                        value: flow.value.expect("keyword produces a value"),
                    },
                ));
            }
            Argument::KeywordSplat(value) => {
                let flow = self.lower_expr(value, block);
                if !flow.reachable {
                    return None;
                }
                ArgumentOperand::KeywordSplat(flow.value.expect("keyword splat produces a value"))
            }
        };
        Some((block, operand))
    }

    fn lower_array(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        elements: Vec<hir::ArrayElement>,
    ) -> Flow {
        let mut block = block;
        let mut lowered = Vec::new();
        for element in elements {
            let (value, splat_span) = match element {
                hir::ArrayElement::Value(value) => (value, None),
                hir::ArrayElement::Splat { value, span } => (value, Some(span)),
            };
            let flow = self.lower_expr(value, block);
            if !flow.reachable {
                return self.abrupt(expression, flow.block);
            }
            block = flow.block;
            let value = flow.value.expect("array element produces a value");
            lowered.push(match splat_span {
                Some(span) => ArrayOperand::Splat { value, span },
                None => ArrayOperand::Value(value),
            });
        }
        let value = self.emit(
            block,
            span,
            OperationKind::BuildArray { elements: lowered },
            true,
        );
        self.normal(expression, block, value)
    }

    fn lower_hash(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        elements: Vec<hir::HashElement>,
    ) -> Flow {
        let mut block = block;
        let mut lowered = Vec::new();
        for element in elements {
            match element {
                hir::HashElement::Pair { key, value } => {
                    let key_flow = self.lower_expr(key, block);
                    if !key_flow.reachable {
                        return self.abrupt(expression, key_flow.block);
                    }
                    let value_flow = self.lower_expr(value, key_flow.block);
                    if !value_flow.reachable {
                        return self.abrupt(expression, value_flow.block);
                    }
                    block = value_flow.block;
                    lowered.push(HashOperand::Pair {
                        key: key_flow.value.expect("hash key produces a value"),
                        value: value_flow.value.expect("hash value produces a value"),
                    });
                }
                hir::HashElement::Splat { value, span } => {
                    let flow = self.lower_expr(value, block);
                    if !flow.reachable {
                        return self.abrupt(expression, flow.block);
                    }
                    block = flow.block;
                    lowered.push(HashOperand::Splat {
                        value: flow.value.expect("hash splat produces a value"),
                        span,
                    });
                }
            }
        }
        let value = self.emit(
            block,
            span,
            OperationKind::BuildHash { elements: lowered },
            true,
        );
        self.normal(expression, block, value)
    }

    fn lower_if(
        &mut self,
        expression: ExprId,
        block: BlockId,
        condition: ExprId,
        then_body: ExprId,
        else_body: Option<ExprId>,
    ) -> Flow {
        let condition_flow = self.lower_expr(condition, block);
        if !condition_flow.reachable {
            return self.abrupt(expression, condition_flow.block);
        }
        let condition_value = condition_flow.value.expect("condition produces a value");
        let then_block = self.new_block_like(condition_flow.block);
        let else_block = self.new_block_like(condition_flow.block);
        let join = self.new_block_like(condition_flow.block);
        let joined = self.add_parameter(join);
        self.branch(
            condition_flow.block,
            condition_value,
            then_block,
            else_block,
        );
        self.cfg.conditionals.push(Conditional {
            expression,
            condition,
            then_body,
            else_body,
            truthy: then_block,
            falsy: else_block,
            join,
        });

        let then_flow = self.lower_expr(then_body, then_block);
        if then_flow.reachable {
            self.jump(
                then_flow.block,
                join,
                vec![then_flow.value.expect("then branch produces a value")],
            );
        } else {
            self.record_terminal_return(then_flow.block, expression);
        }

        let else_flow = match else_body {
            Some(body) => self.lower_expr(body, else_block),
            None => {
                let nil = self.emit(
                    else_block,
                    self.span(expression),
                    OperationKind::Const {
                        value: hir::Literal::Nil,
                    },
                    true,
                );
                self.normal(expression, else_block, nil)
            }
        };
        if else_flow.reachable {
            self.jump(
                else_flow.block,
                join,
                vec![else_flow.value.expect("else branch produces a value")],
            );
        } else {
            self.record_terminal_return(else_flow.block, expression);
        }

        let reachable = then_flow.reachable || else_flow.reachable;
        if reachable {
            self.normal(expression, join, Some(joined))
        } else {
            self.abrupt(expression, join)
        }
    }

    fn lower_assignment(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        target: AssignTarget,
        value: ExprId,
        operator: AssignOperator,
    ) -> Flow {
        let Some((mut block, runtime)) = self.lower_target_runtime(block, target) else {
            return self.abrupt(expression, block);
        };

        match operator {
            AssignOperator::Set => {
                let value_flow = self.lower_expr(value, block);
                if !value_flow.reachable {
                    return self.abrupt(expression, value_flow.block);
                }
                block = value_flow.block;
                let value = value_flow.value.expect("assignment produces a value");
                let result = self.write_runtime(block, span, runtime, value);
                self.normal(expression, result.0, result.1)
            }
            AssignOperator::And | AssignOperator::Or => {
                let read_flow = self.read_runtime(block, span, runtime.clone());
                let Some(old) = read_flow.value else {
                    return self.abrupt(expression, read_flow.block);
                };
                let rhs_block = self.new_block_like(read_flow.block);
                let existing_block = self.new_block_like(read_flow.block);
                let join = self.new_block_like(read_flow.block);
                let joined = self.add_parameter(join);
                let predicate = self.emit(
                    read_flow.block,
                    span,
                    OperationKind::PatternTest {
                        value: old,
                        pattern: Pattern::Truthy,
                    },
                    true,
                );
                let predicate = predicate.expect("truthiness test produces a value");
                match operator {
                    AssignOperator::And => {
                        self.branch(read_flow.block, predicate, rhs_block, existing_block)
                    }
                    AssignOperator::Or => {
                        self.branch(read_flow.block, predicate, existing_block, rhs_block)
                    }
                    _ => unreachable!(),
                }
                self.jump(existing_block, join, vec![old]);

                let rhs_flow = self.lower_expr(value, rhs_block);
                if rhs_flow.reachable {
                    let rhs_value = rhs_flow.value.expect("assignment RHS produces a value");
                    let written = self.write_runtime(rhs_flow.block, span, runtime, rhs_value);
                    self.jump(
                        written.0,
                        join,
                        vec![written.1.expect("assignment write produces a value")],
                    );
                }
                self.normal(expression, join, Some(joined))
            }
            AssignOperator::Binary(operator) => {
                let read_flow = self.read_runtime(block, span, runtime.clone());
                let Some(old) = read_flow.value else {
                    return self.abrupt(expression, read_flow.block);
                };
                let rhs_flow = self.lower_expr(value, read_flow.block);
                if !rhs_flow.reachable {
                    return self.abrupt(expression, rhs_flow.block);
                }
                let rhs = rhs_flow.value.expect("assignment RHS produces a value");
                let computed = self.emit(
                    rhs_flow.block,
                    span,
                    OperationKind::Call {
                        receiver: ReceiverOperand::Value(old),
                        name: operator,
                        arguments: vec![ArgumentOperand::Positional(rhs)],
                        block: None,
                        safe_navigation: false,
                    },
                    true,
                );
                let computed = computed.expect("binary assignment produces a value");
                let written = self.write_runtime(rhs_flow.block, span, runtime, computed);
                self.normal(expression, written.0, written.1)
            }
        }
    }

    fn lower_target_runtime(
        &mut self,
        block: BlockId,
        target: AssignTarget,
    ) -> Option<(BlockId, TargetRuntime)> {
        match target {
            AssignTarget::Local(local) => Some((block, TargetRuntime::Place(Place::Local(local)))),
            AssignTarget::InstanceVariable(name) => {
                Some((block, TargetRuntime::Place(Place::InstanceVariable(name))))
            }
            AssignTarget::ClassVariable(name) => {
                Some((block, TargetRuntime::Place(Place::ClassVariable(name))))
            }
            AssignTarget::Global(name) => Some((block, TargetRuntime::Place(Place::Global(name)))),
            AssignTarget::Constant(path) => {
                Some((block, TargetRuntime::Place(Place::Constant(path))))
            }
            AssignTarget::Attribute { receiver, name } => {
                let flow = self.lower_expr(receiver, block);
                flow.reachable.then(|| {
                    (
                        flow.block,
                        TargetRuntime::Attribute {
                            receiver: flow.value.expect("attribute receiver produces a value"),
                            name,
                        },
                    )
                })
            }
            AssignTarget::Index {
                receiver,
                arguments,
            } => {
                let receiver_flow = self.lower_expr(receiver, block);
                if !receiver_flow.reachable {
                    return None;
                }
                let mut block = receiver_flow.block;
                let mut lowered = Vec::new();
                for argument in arguments {
                    let (next, operand) = self.lower_argument(block, argument)?;
                    block = next;
                    lowered.push(operand);
                }
                Some((
                    block,
                    TargetRuntime::Index {
                        receiver: receiver_flow
                            .value
                            .expect("index receiver produces a value"),
                        arguments: lowered,
                    },
                ))
            }
        }
    }

    fn read_runtime(&mut self, block: BlockId, span: Span, runtime: TargetRuntime) -> Flow {
        match runtime {
            TargetRuntime::Place(place) => {
                let value = self.emit(block, span, OperationKind::Read { place }, true);
                Flow {
                    block,
                    value,
                    reachable: true,
                }
            }
            TargetRuntime::Attribute { receiver, name } => {
                let value = self.emit(
                    block,
                    span,
                    OperationKind::Call {
                        receiver: ReceiverOperand::Value(receiver),
                        name,
                        arguments: Vec::new(),
                        block: None,
                        safe_navigation: false,
                    },
                    true,
                );
                Flow {
                    block,
                    value,
                    reachable: true,
                }
            }
            TargetRuntime::Index {
                receiver,
                arguments,
            } => {
                let value = self.emit(
                    block,
                    span,
                    OperationKind::Call {
                        receiver: ReceiverOperand::Value(receiver),
                        name: hir::Name::new("[]"),
                        arguments,
                        block: None,
                        safe_navigation: false,
                    },
                    true,
                );
                Flow {
                    block,
                    value,
                    reachable: true,
                }
            }
        }
    }

    fn write_runtime(
        &mut self,
        block: BlockId,
        span: Span,
        runtime: TargetRuntime,
        value: ValueId,
    ) -> (BlockId, Option<ValueId>) {
        match runtime {
            TargetRuntime::Place(place) => {
                let result = self.emit(block, span, OperationKind::Write { place, value }, false);
                (block, result.or(Some(value)))
            }
            TargetRuntime::Attribute { receiver, name } => {
                let mut setter = name.as_str().to_owned();
                setter.push('=');
                let result = self.emit(
                    block,
                    span,
                    OperationKind::Call {
                        receiver: ReceiverOperand::Value(receiver),
                        name: hir::Name::new(setter),
                        arguments: vec![ArgumentOperand::Positional(value)],
                        block: None,
                        safe_navigation: false,
                    },
                    true,
                );
                (block, result)
            }
            TargetRuntime::Index {
                receiver,
                mut arguments,
            } => {
                arguments.push(ArgumentOperand::Positional(value));
                let result = self.emit(
                    block,
                    span,
                    OperationKind::Call {
                        receiver: ReceiverOperand::Value(receiver),
                        name: hir::Name::new("[]="),
                        arguments,
                        block: None,
                        safe_navigation: false,
                    },
                    true,
                );
                (block, result)
            }
        }
    }

    fn lower_case(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        case: hir::CaseExpr,
    ) -> Flow {
        let (mut block, scrutinee) = match case.scrutinee {
            Some(scrutinee) => {
                let flow = self.lower_expr(scrutinee, block);
                if !flow.reachable {
                    return self.abrupt(expression, flow.block);
                }
                (flow.block, flow.value)
            }
            None => (block, None),
        };
        let join = self.new_block_like(block);
        let joined = self.add_parameter(join);
        let mut any_normal = false;

        for arm in case.arms {
            let body_block = self.new_block_like(block);
            let next_arm = self.new_block_like(block);
            let mut test = block;
            if arm.conditions.is_empty() {
                self.jump(test, body_block, Vec::new());
            } else {
                for (index, condition) in arm.conditions.iter().copied().enumerate() {
                    let condition_flow = self.lower_expr(condition, test);
                    if !condition_flow.reachable {
                        break;
                    }
                    let condition_value = condition_flow.value.expect("case condition value");
                    let pattern = match scrutinee {
                        Some(_scrutinee) => Pattern::Case {
                            condition: condition_value,
                            expression: condition,
                        },
                        None => Pattern::Truthy,
                    };
                    let matched = self.emit(
                        condition_flow.block,
                        span,
                        OperationKind::PatternTest {
                            value: scrutinee.unwrap_or(condition_value),
                            pattern,
                        },
                        true,
                    );
                    let false_target = if index + 1 == arm.conditions.len() {
                        next_arm
                    } else {
                        self.new_block_like(condition_flow.block)
                    };
                    self.branch(
                        condition_flow.block,
                        matched.expect("case pattern test value"),
                        body_block,
                        false_target,
                    );
                    test = false_target;
                }
            }
            let body_flow = self.lower_expr(arm.body, body_block);
            if body_flow.reachable {
                any_normal = true;
                self.jump(
                    body_flow.block,
                    join,
                    vec![body_flow.value.expect("case body value")],
                );
            }
            block = next_arm;
        }

        let else_flow = match case.else_body {
            Some(else_body) => self.lower_expr(else_body, block),
            None => {
                let nil = self.emit(
                    block,
                    span,
                    OperationKind::Const {
                        value: hir::Literal::Nil,
                    },
                    true,
                );
                self.normal(expression, block, nil)
            }
        };
        if else_flow.reachable {
            any_normal = true;
            self.jump(
                else_flow.block,
                join,
                vec![else_flow.value.expect("case else value")],
            );
        }
        if any_normal {
            self.normal(expression, join, Some(joined))
        } else {
            self.abrupt(expression, join)
        }
    }

    fn lower_loop(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        loop_expr: LoopExpr,
    ) -> Flow {
        let header = self.new_block_like(block);
        let condition = self.new_block_like(header);
        let body = self.new_block_like(header);
        let normal_exit = self.new_block_like(header);
        let exit = self.new_block_like(header);
        let exit_value = self.add_parameter(exit);
        // The header parameter carries `next` values. The current loop model
        // does not consume it, but retaining it makes the transfer explicit.
        let _header_value = self.add_parameter(header);
        let initial = self.emit(
            block,
            span,
            OperationKind::Const {
                value: hir::Literal::Nil,
            },
            true,
        );
        self.jump(
            block,
            header,
            vec![initial.expect("loop header seed produces a value")],
        );
        self.jump(header, condition, Vec::new());

        let condition_flow = self.lower_expr(loop_expr.condition, condition);
        if condition_flow.reachable {
            let condition_value = condition_flow.value.expect("loop condition value");
            match loop_expr.kind {
                LoopKind::Until => {
                    self.branch(condition_flow.block, condition_value, normal_exit, body)
                }
                LoopKind::While | LoopKind::For => {
                    self.branch(condition_flow.block, condition_value, body, normal_exit)
                }
            }
        }

        self.loops.push(LoopContext {
            break_target: exit,
            next_target: header,
        });
        let body_flow = match loop_expr.body {
            Some(body_expression) => self.lower_expr(body_expression, body),
            None => {
                let nil = self.emit(
                    body,
                    span,
                    OperationKind::Const {
                        value: hir::Literal::Nil,
                    },
                    true,
                );
                self.normal(expression, body, nil)
            }
        };
        self.loops.pop();
        if body_flow.reachable {
            let seed = self.emit(
                body_flow.block,
                span,
                OperationKind::Const {
                    value: hir::Literal::Nil,
                },
                true,
            );
            self.jump(
                body_flow.block,
                header,
                vec![seed.expect("loop back-edge seed produces a value")],
            );
        }
        let normal = self.emit(
            normal_exit,
            span,
            OperationKind::Const {
                value: hir::Literal::Nil,
            },
            true,
        );
        self.jump(
            normal_exit,
            exit,
            vec![normal.expect("loop exit produces a value")],
        );
        self.normal(expression, exit, Some(exit_value))
    }

    fn lower_return(&mut self, expression: ExprId, block: BlockId, value: Option<ExprId>) -> Flow {
        let (block, value) = self.lower_optional_value(block, value);
        let value = value.unwrap_or_else(|| {
            self.emit(
                block,
                self.span(expression),
                OperationKind::Const {
                    value: hir::Literal::Nil,
                },
                true,
            )
            .expect("return seed produces a value")
        });
        self.emit(
            block,
            self.span(expression),
            OperationKind::Record { value: Some(value) },
            false,
        );
        self.set_terminator(block, Terminator::Return(Some(value)));
        self.abrupt(expression, block)
    }

    fn lower_break(&mut self, expression: ExprId, block: BlockId, value: Option<ExprId>) -> Flow {
        let Some(context) = self.loops.last().copied() else {
            return self.lower_unsupported_transfer(expression, block, "break-outside-loop");
        };
        let (block, value) = self.lower_optional_value(block, value);
        let value = value.unwrap_or_else(|| {
            self.emit(
                block,
                self.span(expression),
                OperationKind::Const {
                    value: hir::Literal::Nil,
                },
                true,
            )
            .expect("break seed produces a value")
        });
        self.jump(block, context.break_target, vec![value]);
        self.abrupt(expression, block)
    }

    fn lower_next(&mut self, expression: ExprId, block: BlockId, value: Option<ExprId>) -> Flow {
        let Some(context) = self.loops.last().copied() else {
            return self.lower_unsupported_transfer(expression, block, "next-outside-loop");
        };
        let (block, value) = self.lower_optional_value(block, value);
        let value = value.unwrap_or_else(|| {
            self.emit(
                block,
                self.span(expression),
                OperationKind::Const {
                    value: hir::Literal::Nil,
                },
                true,
            )
            .expect("next seed produces a value")
        });
        self.jump(block, context.next_target, vec![value]);
        self.abrupt(expression, block)
    }

    fn lower_optional_value(
        &mut self,
        block: BlockId,
        value: Option<ExprId>,
    ) -> (BlockId, Option<ValueId>) {
        let Some(value) = value else {
            return (block, None);
        };
        let flow = self.lower_expr(value, block);
        if flow.reachable {
            (flow.block, flow.value)
        } else {
            (flow.block, None)
        }
    }

    fn lower_retry(&mut self, expression: ExprId, block: BlockId, span: Span) -> Flow {
        let Some(context) = self.rescues.last().copied() else {
            return self.lower_unsupported_transfer(expression, block, "retry-outside-rescue");
        };
        let _ = self.emit(block, span, OperationKind::Record { value: None }, false);
        self.jump(block, context.retry_target, Vec::new());
        let _ = span;
        self.abrupt(expression, block)
    }

    fn lower_unsupported_transfer(
        &mut self,
        expression: ExprId,
        block: BlockId,
        kind: &str,
    ) -> Flow {
        let value = self.emit(
            block,
            self.span(expression),
            OperationKind::Unsupported {
                kind: hir::Name::new(kind),
            },
            true,
        );
        self.normal(expression, block, value)
    }

    fn lower_begin(
        &mut self,
        expression: ExprId,
        block: BlockId,
        span: Span,
        begin: BeginExpr,
    ) -> Flow {
        let outer_unwind = self.unwind(block);
        let after = self.new_block_with_unwind(outer_unwind);
        let after_value = self.add_parameter(after);
        let ensure_entry = begin
            .ensure
            .as_ref()
            .map(|_| self.new_block_with_unwind(outer_unwind));
        if let Some(ensure_entry) = ensure_entry {
            self.cfg.ensure_entries.push(ensure_entry);
        }
        let ensure_value = ensure_entry.map(|entry| self.add_parameter(entry));
        let rescue_unwind = ensure_entry.or(outer_unwind);
        let rescue_entry =
            (!begin.rescue.is_empty()).then(|| self.new_block_with_unwind(rescue_unwind));
        let protected_unwind = rescue_entry.or(ensure_entry).or(outer_unwind);
        let body_start = self.new_block_with_unwind(protected_unwind);
        self.jump(block, body_start, Vec::new());

        let body_flow = match begin.body {
            Some(body) => self.lower_expr(body, body_start),
            None => {
                let nil = self.emit(
                    body_start,
                    span,
                    OperationKind::Const {
                        value: hir::Literal::Nil,
                    },
                    true,
                );
                self.normal(expression, body_start, nil)
            }
        };

        let finish_normal = |builder: &mut Self, flow: Flow, value: ValueId| {
            if let Some(ensure_entry) = ensure_entry {
                builder.jump(flow.block, ensure_entry, vec![value]);
            } else {
                builder.jump(flow.block, after, vec![value]);
            }
        };

        if body_flow.reachable {
            let mut normal_flow = body_flow;
            if let Some(else_body) = begin.else_body {
                let else_block = builder_new_block_like(self, normal_flow.block, rescue_unwind);
                self.jump(normal_flow.block, else_block, Vec::new());
                normal_flow = self.lower_expr(else_body, else_block);
            }
            if normal_flow.reachable {
                finish_normal(
                    self,
                    normal_flow,
                    normal_flow.value.expect("begin body produces a value"),
                );
            }
        }

        if let Some(rescue_entry) = rescue_entry {
            let exception = self.add_parameter(rescue_entry);
            self.rescues.push(RescueContext {
                retry_target: body_start,
            });
            let mut test = rescue_entry;
            let rescue_count = begin.rescue.len();
            for (index, clause) in begin.rescue.into_iter().enumerate() {
                let body = self.new_block_with_unwind(rescue_unwind);
                let next = if index + 1 == rescue_count {
                    None
                } else {
                    Some(self.new_block_with_unwind(rescue_unwind))
                };
                if clause.exceptions.is_empty() {
                    self.jump(test, body, Vec::new());
                } else {
                    for (condition_index, condition) in
                        clause.exceptions.iter().copied().enumerate()
                    {
                        let condition_flow = self.lower_expr(condition, test);
                        if !condition_flow.reachable {
                            break;
                        }
                        let condition_value = condition_flow.value.expect("rescue condition value");
                        let pattern = Pattern::Case {
                            condition: condition_value,
                            expression: condition,
                        };
                        let matched = self.emit(
                            condition_flow.block,
                            span,
                            OperationKind::PatternTest {
                                value: exception,
                                pattern,
                            },
                            true,
                        );
                        let false_target = if condition_index + 1 == clause.exceptions.len() {
                            next.unwrap_or_else(|| self.new_block_with_unwind(rescue_unwind))
                        } else {
                            self.new_block_with_unwind(rescue_unwind)
                        };
                        self.branch(
                            condition_flow.block,
                            matched.expect("rescue pattern test value"),
                            body,
                            false_target,
                        );
                        test = false_target;
                    }
                }
                if let Some(reference) = clause.reference {
                    self.emit(
                        body,
                        span,
                        OperationKind::Write {
                            place: Place::Local(reference),
                            value: exception,
                        },
                        false,
                    );
                }
                let body_flow = match clause.body {
                    Some(body_expression) => self.lower_expr(body_expression, body),
                    None => {
                        let nil = self.emit(
                            body,
                            span,
                            OperationKind::Const {
                                value: hir::Literal::Nil,
                            },
                            true,
                        );
                        self.normal(expression, body, nil)
                    }
                };
                if body_flow.reachable {
                    finish_normal(
                        self,
                        body_flow,
                        body_flow.value.expect("rescue body produces a value"),
                    );
                }
                if let Some(next) = next {
                    test = next;
                } else if !self.closed[test.0 as usize] {
                    self.set_terminator(test, Terminator::Raise(exception));
                }
            }
            self.rescues.pop();
        }

        if let Some(ensure_entry) = ensure_entry {
            let ensure_flow = match begin.ensure {
                Some(ensure_body) => self.lower_expr(ensure_body, ensure_entry),
                None => self.normal(
                    expression,
                    ensure_entry,
                    Some(ensure_value.expect("ensure value")),
                ),
            };
            if ensure_flow.reachable {
                self.set_terminator(
                    ensure_flow.block,
                    Terminator::EnsureComplete {
                        expression,
                        target: after,
                        arguments: vec![ensure_value.expect("ensure value")],
                    },
                );
            }
        }
        let _ = self.emit(
            after,
            span,
            OperationKind::Record {
                value: Some(after_value),
            },
            false,
        );
        self.normal(expression, after, Some(after_value))
    }

    fn span(&self, expression: ExprId) -> Span {
        self.program
            .expression(expression)
            .map(|expr| expr.span)
            .unwrap_or(Span::new(hir::FileId(0), 0, 0))
    }
}

fn builder_new_block_like(
    builder: &mut Builder<'_>,
    block: BlockId,
    unwind: Option<BlockId>,
) -> BlockId {
    let _ = block;
    builder.new_block_with_unwind(unwind)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transfer_graphs_retain_expression_identity_without_value_tables() {
        let source = b"value = 1\nvalue.to_s\n";
        let program = hir::lower(hir::FileId(0), source);
        let graphs = build_all_for_index(&program);
        let graph = graphs.first().expect("root graph");
        assert!(graph.expression_values.is_empty());
        assert!(graph
            .blocks
            .iter()
            .flat_map(|block| &block.operations)
            .any(
                |operation| matches!(operation.kind, OperationKind::Call { .. })
                    && operation.expression.is_some()
            ));
    }
}
