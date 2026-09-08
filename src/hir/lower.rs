//! Prism-to-HIR lowering.
//!
//! The lowerer is deliberately a syntax adapter. It copies all information
//! needed by later phases into owned HIR values and never exposes a Prism node
//! in the resulting [`Program`]. Nodes that are not yet represented by a
//! semantic HIR variant become [`ExprKind::Unsupported`] with their original
//! span instead of disappearing.

use super::{
    Argument, ArrayElement, AssignOperator, AssignTarget, BeginExpr, Body, BodyId, BodyOwner,
    CaseArm, CaseExpr, Closure, ClosureId, ClosureKind, ConstantPath, DeclId, Declaration,
    DeclarationKind, Expr, ExprId, ExprKind, FileId, HashElement, Literal, LocalId, LoopExpr,
    LoopKind, Name, Parameter, ParameterKind, Parameters, Program, Read, Receiver, RescueClause,
    ScopeId, Span, Unsupported,
};
use crate::prism;
use ruby_prism::{ArgumentsNode, CallNode, Node, ParametersNode, Visit};
use std::collections::{HashMap, HashSet};

/// Lower one parsed Ruby source buffer into an owned HIR program.
#[must_use]
pub fn lower(file: FileId, source: &[u8]) -> Program {
    let parsed = ruby_prism::parse(source);
    let root = parsed.node();
    Lowerer::new(file, source).lower_root(&root)
}

struct Scope {
    id: ScopeId,
    locals: HashMap<String, LocalId>,
}

struct Lowerer<'src> {
    file: FileId,
    source: &'src [u8],
    program: Program,
    scopes: Vec<Scope>,
    lowered_call_spans: HashSet<(usize, usize)>,
    lowered_assignment_spans: HashSet<(usize, usize)>,
    next_local: u32,
    next_scope: u32,
}

impl<'src> Lowerer<'src> {
    fn new(file: FileId, source: &'src [u8]) -> Self {
        Self {
            file,
            source,
            program: Program {
                file: Some(file),
                ..Program::default()
            },
            scopes: Vec::new(),
            lowered_call_spans: HashSet::new(),
            lowered_assignment_spans: HashSet::new(),
            next_local: 0,
            next_scope: 0,
        }
    }

    fn lower_root(mut self, root: &Node<'_>) -> Program {
        self.push_scope();
        let root_expr = self.lower_node(root);
        self.lower_nested_expressions(root);
        let body = self.push_body(
            BodyOwner::TopLevel,
            Parameters::default(),
            root_expr,
            self.span(root),
        );
        self.pop_scope();
        self.program.root = Some(body);
        self.program
    }

    fn span(&self, node: &Node<'_>) -> Span {
        let location = node.location();
        self.span_location(location)
    }

    fn span_location(&self, location: ruby_prism::Location<'_>) -> Span {
        self.span_offsets(location.start_offset(), location.end_offset())
    }

    fn span_offsets(&self, start: usize, end: usize) -> Span {
        Span::new(
            self.file,
            u32::try_from(start).unwrap_or(u32::MAX),
            u32::try_from(end).unwrap_or(u32::MAX),
        )
    }

    fn text(&self, node: &Node<'_>) -> String {
        prism::text(self.source, node)
    }

    fn push_expr(&mut self, node: &Node<'_>, kind: ExprKind) -> ExprId {
        let id = ExprId(self.program.expressions.len() as u32);
        self.program.expressions.push(Expr {
            span: self.span(node),
            kind,
        });
        id
    }

    fn push_expr_with_span(&mut self, span: Span, kind: ExprKind) -> ExprId {
        let id = ExprId(self.program.expressions.len() as u32);
        self.program.expressions.push(Expr { span, kind });
        id
    }

    fn push_body(
        &mut self,
        owner: BodyOwner,
        parameters: Parameters,
        root: ExprId,
        span: Span,
    ) -> BodyId {
        let id = BodyId(self.program.bodies.len() as u32);
        self.program.bodies.push(Body {
            owner,
            parameters,
            root,
            span,
        });
        id
    }

    fn push_scope(&mut self) -> ScopeId {
        let id = ScopeId(self.next_scope);
        self.next_scope = self.next_scope.saturating_add(1);
        self.scopes.push(Scope {
            id,
            locals: HashMap::new(),
        });
        id
    }

    fn pop_scope(&mut self) {
        let _ = self.scopes.pop();
    }

    fn current_scope(&self) -> ScopeId {
        self.scopes.last().map_or(ScopeId(0), |scope| scope.id)
    }

    fn local(&mut self, name: &str) -> LocalId {
        for scope in self.scopes.iter().rev() {
            if let Some(local) = scope.locals.get(name) {
                return *local;
            }
        }
        let local = self.allocate_local(name);
        if let Some(scope) = self.scopes.last_mut() {
            scope.locals.insert(name.to_owned(), local);
        }
        local
    }

    fn new_local(&mut self, name: &str) -> LocalId {
        let local = self.allocate_local(name);
        if let Some(scope) = self.scopes.last_mut() {
            scope.locals.insert(name.to_owned(), local);
        }
        local
    }

    fn allocate_local(&mut self, name: &str) -> LocalId {
        let local = LocalId(self.next_local);
        self.next_local = self.next_local.saturating_add(1);
        self.program.locals.push(Name::new(name));
        local
    }

    fn nil(&mut self, node: &Node<'_>) -> ExprId {
        self.push_expr(node, ExprKind::Nil)
    }

    fn unsupported(&mut self, node: &Node<'_>) -> ExprId {
        let expression = self.push_expr(
            node,
            ExprKind::Unsupported(Unsupported {
                kind: Name::new("prism-node"),
                children: Vec::new(),
            }),
        );
        let children = self.lower_nested_expressions(node);
        if let Some(Expr {
            kind: ExprKind::Unsupported(unsupported),
            ..
        }) = self.program.expressions.get_mut(expression.0 as usize)
        {
            unsupported.children = children;
        }
        expression
    }

    /// Unsupported parents still contain executable expressions. Keep calls
    /// and assignments available to the migration adapter instead of making
    /// their source span fall back to Prism evaluation solely because the
    /// parent syntax has not acquired a dedicated HIR variant yet.
    fn lower_nested_expressions(&mut self, node: &Node<'_>) -> Vec<ExprId> {
        let mut visitor = NestedExpressionLowerer {
            lowerer: self,
            expressions: Vec::new(),
        };
        visitor.visit(node);
        visitor.expressions
    }

    fn is_assignment_node(node: &Node<'_>) -> bool {
        node.as_local_variable_write_node().is_some()
            || node.as_local_variable_operator_write_node().is_some()
            || node.as_local_variable_and_write_node().is_some()
            || node.as_local_variable_or_write_node().is_some()
            || node.as_instance_variable_write_node().is_some()
            || node.as_instance_variable_operator_write_node().is_some()
            || node.as_instance_variable_and_write_node().is_some()
            || node.as_instance_variable_or_write_node().is_some()
            || node.as_class_variable_write_node().is_some()
            || node.as_class_variable_operator_write_node().is_some()
            || node.as_class_variable_and_write_node().is_some()
            || node.as_class_variable_or_write_node().is_some()
            || node.as_global_variable_write_node().is_some()
            || node.as_global_variable_operator_write_node().is_some()
            || node.as_global_variable_and_write_node().is_some()
            || node.as_global_variable_or_write_node().is_some()
            || node.as_constant_write_node().is_some()
            || node.as_constant_operator_write_node().is_some()
            || node.as_constant_and_write_node().is_some()
            || node.as_constant_or_write_node().is_some()
            || node.as_constant_path_write_node().is_some()
            || node.as_constant_path_operator_write_node().is_some()
            || node.as_constant_path_and_write_node().is_some()
            || node.as_constant_path_or_write_node().is_some()
            || node.as_index_operator_write_node().is_some()
            || node.as_index_and_write_node().is_some()
            || node.as_index_or_write_node().is_some()
            || node.as_call_operator_write_node().is_some()
            || node.as_call_and_write_node().is_some()
            || node.as_call_or_write_node().is_some()
            || node
                .as_call_node()
                .is_some_and(|call| call.is_attribute_write())
    }

    fn is_special_call_node(node: &Node<'_>) -> bool {
        node.as_yield_node().is_some()
            || node.as_super_node().is_some()
            || node.as_forwarding_super_node().is_some()
    }

    fn lower_node(&mut self, node: &Node<'_>) -> ExprId {
        if let Some(program) = node.as_program_node() {
            return self.lower_node(&program.statements().as_node());
        }
        if let Some(statements) = node.as_statements_node() {
            let expressions = statements
                .body()
                .into_iter()
                .map(|child| self.lower_node(&child))
                .collect::<Vec<_>>();
            return self.push_expr(node, ExprKind::Sequence(expressions));
        }
        if let Some(definition) = node.as_def_node() {
            return self.lower_definition(node, &definition);
        }
        if let Some(class) = node.as_class_node() {
            return self.lower_class(node, &class);
        }
        if let Some(module) = node.as_module_node() {
            return self.lower_module(node, &module);
        }
        if let Some(singleton) = node.as_singleton_class_node() {
            return self.lower_singleton_class(node, &singleton);
        }

        // Assignment nodes must be recognized before ordinary calls. Their
        // target and operator are semantically significant and must not be
        // flattened into a setter send during lowering.
        if let Some(write) = node.as_local_variable_write_node() {
            let local = self.local(&prism::constant_name(write.name()));
            return self.lower_assignment(
                node,
                AssignTarget::Local(local),
                write.value(),
                AssignOperator::Set,
            );
        }
        if let Some(write) = node.as_local_variable_operator_write_node() {
            let local = self.local(&prism::constant_name(write.name()));
            return self.lower_assignment(
                node,
                AssignTarget::Local(local),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_local_variable_and_write_node() {
            let local = self.local(&prism::constant_name(write.name()));
            return self.lower_assignment(
                node,
                AssignTarget::Local(local),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_local_variable_or_write_node() {
            let local = self.local(&prism::constant_name(write.name()));
            return self.lower_assignment(
                node,
                AssignTarget::Local(local),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_instance_variable_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::InstanceVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Set,
            );
        }
        if let Some(write) = node.as_instance_variable_operator_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::InstanceVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_instance_variable_and_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::InstanceVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_instance_variable_or_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::InstanceVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_class_variable_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::ClassVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Set,
            );
        }
        if let Some(write) = node.as_class_variable_operator_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::ClassVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_class_variable_and_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::ClassVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_class_variable_or_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::ClassVariable(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_global_variable_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Global(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Set,
            );
        }
        if let Some(write) = node.as_global_variable_operator_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Global(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_global_variable_and_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Global(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_global_variable_or_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Global(Name::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_constant_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Set,
            );
        }
        if let Some(write) = node.as_constant_operator_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_constant_and_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_constant_or_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(prism::constant_name(write.name()))),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_constant_path_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(self.text(&write.target().as_node()))),
                write.value(),
                AssignOperator::Set,
            );
        }
        if let Some(write) = node.as_constant_path_operator_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(self.text(&write.target().as_node()))),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_constant_path_and_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(self.text(&write.target().as_node()))),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_constant_path_or_write_node() {
            return self.lower_assignment(
                node,
                AssignTarget::Constant(ConstantPath::new(self.text(&write.target().as_node()))),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_index_operator_write_node() {
            return self.lower_index_assignment(
                node,
                write.receiver(),
                write.arguments(),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_index_and_write_node() {
            return self.lower_index_assignment(
                node,
                write.receiver(),
                write.arguments(),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_index_or_write_node() {
            return self.lower_index_assignment(
                node,
                write.receiver(),
                write.arguments(),
                write.value(),
                AssignOperator::Or,
            );
        }
        if let Some(write) = node.as_call_operator_write_node() {
            return self.lower_attribute_assignment(
                node,
                write.receiver(),
                prism::constant_name(write.write_name()),
                write.value(),
                AssignOperator::Binary(Name::new(prism::constant_name(write.binary_operator()))),
            );
        }
        if let Some(write) = node.as_call_and_write_node() {
            return self.lower_attribute_assignment(
                node,
                write.receiver(),
                prism::constant_name(write.write_name()),
                write.value(),
                AssignOperator::And,
            );
        }
        if let Some(write) = node.as_call_or_write_node() {
            return self.lower_attribute_assignment(
                node,
                write.receiver(),
                prism::constant_name(write.write_name()),
                write.value(),
                AssignOperator::Or,
            );
        }

        if let Some(call) = node.as_call_node() {
            return self.lower_call(node, &call);
        }
        if let Some(super_node) = node.as_super_node() {
            return self.lower_special_call(
                node,
                Receiver::Super,
                "super",
                super_node.arguments(),
                super_node.block(),
                false,
            );
        }
        if let Some(super_node) = node.as_forwarding_super_node() {
            let mut arguments = Vec::new();
            arguments.push(Argument::Forwarded);
            let block = self.lower_block_argument(super_node.block().map(|block| block.as_node()));
            return self.lower_call_parts(
                node,
                Receiver::Super,
                Name::new("super"),
                arguments,
                vec![1],
                vec![self.span(node)],
                block,
                false,
            );
        }
        if let Some(yield_node) = node.as_yield_node() {
            return self.lower_special_call(
                node,
                Receiver::Yield,
                "yield",
                yield_node.arguments(),
                None,
                false,
            );
        }

        if let Some(array) = node.as_array_node() {
            let elements = array
                .elements()
                .into_iter()
                .map(|element| {
                    if let Some(splat) = element.as_splat_node() {
                        if let Some(value) = splat.expression() {
                            ArrayElement::Splat {
                                value: self.lower_node(&value),
                                span: self.span(&element),
                            }
                        } else {
                            ArrayElement::Value(self.lower_node(&element))
                        }
                    } else {
                        ArrayElement::Value(self.lower_node(&element))
                    }
                })
                .collect();
            return self.push_expr(node, ExprKind::Array(elements));
        }
        if let Some(hash) = node.as_hash_node() {
            return self.lower_hash(node, hash.elements());
        }
        if let Some(hash) = node.as_keyword_hash_node() {
            return self.lower_hash(node, hash.elements());
        }
        if let Some(parentheses) = node.as_parentheses_node() {
            return if let Some(body) = parentheses.body() {
                self.lower_node(&body)
            } else {
                self.nil(node)
            };
        }
        if let Some(block) = node.as_block_node() {
            let closure =
                self.lower_closure(node, block.parameters(), block.body(), ClosureKind::Block);
            return self.push_expr(node, ExprKind::Closure(closure));
        }
        if let Some(lambda) = node.as_lambda_node() {
            let closure = self.lower_closure(
                node,
                lambda.parameters(),
                lambda.body(),
                ClosureKind::Lambda,
            );
            return self.push_expr(node, ExprKind::Closure(closure));
        }
        if let Some(if_node) = node.as_if_node() {
            let condition = self.lower_node(&if_node.predicate());
            let then_body = if let Some(body) = if_node.statements() {
                self.lower_node(&body.as_node())
            } else {
                self.nil(node)
            };
            let else_body = if_node
                .subsequent()
                .map(|subsequent| self.lower_node(&subsequent));
            return self.push_expr(
                node,
                ExprKind::If {
                    condition,
                    then_body,
                    else_body,
                },
            );
        }
        if let Some(unless) = node.as_unless_node() {
            let predicate = self.lower_node(&unless.predicate());
            let condition = self.push_expr_with_span(
                self.program.expressions[predicate.0 as usize].span,
                ExprKind::Call(super::Call {
                    receiver: Receiver::Explicit(predicate),
                    name: Name::new("!"),
                    arguments: Vec::new(),
                    argument_groups: Vec::new(),
                    argument_spans: Vec::new(),
                    block: None,
                    safe_navigation: false,
                    span: self.program.expressions[predicate.0 as usize].span,
                }),
            );
            let then_body = if let Some(body) = unless.statements() {
                self.lower_node(&body.as_node())
            } else {
                self.nil(node)
            };
            let else_body = unless
                .else_clause()
                .and_then(|else_clause| else_clause.statements())
                .map(|statements| self.lower_node(&statements.as_node()));
            return self.push_expr(
                node,
                ExprKind::If {
                    condition,
                    then_body,
                    else_body,
                },
            );
        }
        if let Some(case_node) = node.as_case_node() {
            return self.lower_case(node, &case_node);
        }
        if let Some(return_node) = node.as_return_node() {
            let value = self.lower_control_arguments(return_node.arguments());
            return self.push_expr(node, ExprKind::Return(value));
        }
        if let Some(break_node) = node.as_break_node() {
            let value = self.lower_control_arguments(break_node.arguments());
            return self.push_expr(node, ExprKind::Break(value));
        }
        if let Some(next_node) = node.as_next_node() {
            let value = self.lower_control_arguments(next_node.arguments());
            return self.push_expr(node, ExprKind::Next(value));
        }
        if node.as_retry_node().is_some() {
            return self.push_expr(node, ExprKind::Retry);
        }
        if let Some(for_node) = node.as_for_node() {
            let Some(index) = self.lower_for_target(&for_node.index()) else {
                return self.unsupported(node);
            };
            let condition = self.lower_node(&for_node.collection());
            let body = for_node
                .statements()
                .map(|body| self.lower_node(&body.as_node()));
            return self.push_expr(
                node,
                ExprKind::Loop(LoopExpr {
                    kind: LoopKind::For,
                    condition,
                    body,
                    index: Some(index),
                }),
            );
        }
        if let Some(while_node) = node.as_while_node() {
            let condition = self.lower_node(&while_node.predicate());
            let body = while_node
                .statements()
                .map(|body| self.lower_node(&body.as_node()));
            return self.push_expr(
                node,
                ExprKind::Loop(LoopExpr {
                    kind: LoopKind::While,
                    condition,
                    body,
                    index: None,
                }),
            );
        }
        if let Some(until_node) = node.as_until_node() {
            let condition = self.lower_node(&until_node.predicate());
            let body = until_node
                .statements()
                .map(|body| self.lower_node(&body.as_node()));
            return self.push_expr(
                node,
                ExprKind::Loop(LoopExpr {
                    kind: LoopKind::Until,
                    condition,
                    body,
                    index: None,
                }),
            );
        }
        if let Some(begin) = node.as_begin_node() {
            return self.lower_begin(node, &begin);
        }

        if node.as_nil_node().is_some() {
            return self.push_expr(node, ExprKind::Nil);
        }
        if node.as_true_node().is_some() {
            return self.push_expr(node, ExprKind::Literal(Literal::True));
        }
        if node.as_false_node().is_some() {
            return self.push_expr(node, ExprKind::Literal(Literal::False));
        }
        if let Some(integer) = node.as_integer_node() {
            return self.push_expr(
                node,
                ExprKind::Literal(Literal::Integer(self.text(&integer.as_node()))),
            );
        }
        if node.as_float_node().is_some() {
            return self.push_expr(node, ExprKind::Literal(Literal::Float(self.text(node))));
        }
        if let Some(string) = node.as_string_node() {
            return self.push_expr(
                node,
                ExprKind::Literal(Literal::String(self.text(&string.as_node()))),
            );
        }
        if let Some(symbol) = node.as_symbol_node() {
            return self.push_expr(
                node,
                ExprKind::Literal(Literal::Symbol(
                    String::from_utf8_lossy(symbol.unescaped()).into_owned(),
                )),
            );
        }
        if node.as_rational_node().is_some() {
            return self.push_expr(node, ExprKind::Literal(Literal::Rational(self.text(node))));
        }
        if let Some(imaginary) = node.as_imaginary_node() {
            return self.push_expr(
                node,
                ExprKind::Literal(Literal::Imaginary(self.text(&imaginary.as_node()))),
            );
        }
        if node.as_regular_expression_node().is_some() {
            return self.push_expr(
                node,
                ExprKind::Literal(Literal::RegularExpression(self.text(node))),
            );
        }
        if node.as_x_string_node().is_some() {
            return self.push_expr(node, ExprKind::Literal(Literal::XString(self.text(node))));
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let local = self.local(&prism::constant_name(local.name()));
            return self.push_expr(node, ExprKind::Read(Read::Local(local)));
        }
        if let Some(instance) = node.as_instance_variable_read_node() {
            return self.push_expr(
                node,
                ExprKind::Read(Read::InstanceVariable(Name::new(prism::constant_name(
                    instance.name(),
                )))),
            );
        }
        if let Some(class) = node.as_class_variable_read_node() {
            return self.push_expr(
                node,
                ExprKind::Read(Read::ClassVariable(Name::new(prism::constant_name(
                    class.name(),
                )))),
            );
        }
        if let Some(global) = node.as_global_variable_read_node() {
            return self.push_expr(
                node,
                ExprKind::Read(Read::Global(Name::new(prism::constant_name(global.name())))),
            );
        }
        if node.as_self_node().is_some() {
            return self.push_expr(node, ExprKind::Read(Read::SelfValue));
        }
        if let Some(constant) = node.as_constant_read_node() {
            return self.push_expr(
                node,
                ExprKind::Read(Read::Constant(ConstantPath::new(prism::constant_name(
                    constant.name(),
                )))),
            );
        }
        if node.as_constant_path_node().is_some() {
            return self.push_expr(
                node,
                ExprKind::Read(Read::Constant(ConstantPath::new(self.text(node)))),
            );
        }
        if let Some(numbered) = node.as_numbered_reference_read_node() {
            return self.push_expr(node, ExprKind::Read(Read::Numbered(numbered.number())));
        }
        if node.as_it_local_variable_read_node().is_some() {
            return self.push_expr(node, ExprKind::Read(Read::It));
        }

        self.unsupported(node)
    }

    fn lower_for_target(&mut self, node: &Node<'_>) -> Option<AssignTarget> {
        if let Some(target) = node.as_local_variable_target_node() {
            return Some(AssignTarget::Local(
                self.local(&prism::constant_name(target.name())),
            ));
        }
        if let Some(write) = node.as_local_variable_write_node() {
            return Some(AssignTarget::Local(
                self.local(&prism::constant_name(write.name())),
            ));
        }
        if let Some(target) = node.as_instance_variable_target_node() {
            return Some(AssignTarget::InstanceVariable(Name::new(
                prism::constant_name(target.name()),
            )));
        }
        if let Some(target) = node.as_class_variable_target_node() {
            return Some(AssignTarget::ClassVariable(Name::new(
                prism::constant_name(target.name()),
            )));
        }
        if let Some(target) = node.as_global_variable_target_node() {
            return Some(AssignTarget::Global(Name::new(prism::constant_name(
                target.name(),
            ))));
        }
        if let Some(target) = node.as_constant_target_node() {
            return Some(AssignTarget::Constant(ConstantPath::new(
                prism::constant_name(target.name()),
            )));
        }
        if let Some(target) = node.as_constant_path_target_node() {
            return Some(AssignTarget::Constant(ConstantPath::new(
                self.text(&target.as_node()),
            )));
        }
        None
    }

    fn lower_case(&mut self, node: &Node<'_>, case_node: &ruby_prism::CaseNode<'_>) -> ExprId {
        let scrutinee = case_node
            .predicate()
            .map(|predicate| self.lower_node(&predicate));
        let arms = case_node
            .conditions()
            .into_iter()
            .filter_map(|condition| {
                let when_node = condition.as_when_node()?;
                let conditions = when_node
                    .conditions()
                    .into_iter()
                    .map(|condition| self.lower_node(&condition))
                    .collect();
                let body = when_node
                    .statements()
                    .map(|statements| self.lower_node(&statements.as_node()))
                    .unwrap_or_else(|| self.nil(&condition));
                Some(CaseArm {
                    conditions,
                    body,
                    span: self.span(&condition),
                })
            })
            .collect();
        let else_body = case_node.else_clause().map(|else_clause| {
            else_clause
                .statements()
                .map(|statements| self.lower_node(&statements.as_node()))
                .unwrap_or_else(|| self.nil(&else_clause.as_node()))
        });
        self.push_expr(
            node,
            ExprKind::Case(CaseExpr {
                scrutinee,
                arms,
                else_body,
            }),
        )
    }

    fn lower_assignment(
        &mut self,
        node: &Node<'_>,
        target: AssignTarget,
        value: Node<'_>,
        operator: AssignOperator,
    ) -> ExprId {
        let span = self.span(node);
        self.lowered_assignment_spans
            .insert((span.start as usize, span.end as usize));
        let value = self.lower_node(&value);
        self.push_expr(
            node,
            ExprKind::Assign {
                target,
                target_span: self.span(node),
                value,
                operator,
            },
        )
    }

    fn lower_assignment_with_target_span(
        &mut self,
        node: &Node<'_>,
        target: AssignTarget,
        target_span: Span,
        value: &Node<'_>,
        operator: AssignOperator,
    ) -> ExprId {
        let span = self.span(node);
        self.lowered_assignment_spans
            .insert((span.start as usize, span.end as usize));
        let value = self.lower_node(value);
        self.push_expr(
            node,
            ExprKind::Assign {
                target,
                target_span,
                value,
                operator,
            },
        )
    }

    fn lower_attribute_assignment(
        &mut self,
        node: &Node<'_>,
        receiver: Option<Node<'_>>,
        name: String,
        value: Node<'_>,
        operator: AssignOperator,
    ) -> ExprId {
        let receiver = receiver
            .map(|receiver| self.lower_node(&receiver))
            .unwrap_or_else(|| self.push_expr(node, ExprKind::Read(Read::SelfValue)));
        self.lower_assignment(
            node,
            AssignTarget::Attribute {
                receiver,
                name: Name::new(name.trim_end_matches('=')),
            },
            value,
            operator,
        )
    }

    fn lower_index_assignment(
        &mut self,
        node: &Node<'_>,
        receiver: Option<Node<'_>>,
        arguments: Option<ArgumentsNode<'_>>,
        value: Node<'_>,
        operator: AssignOperator,
    ) -> ExprId {
        let receiver = if let Some(receiver) = receiver {
            self.lower_node(&receiver)
        } else {
            self.push_expr(node, ExprKind::Read(Read::SelfValue))
        };
        let arguments = self.lower_arguments(arguments);
        self.lower_assignment(
            node,
            AssignTarget::Index {
                receiver,
                arguments,
            },
            value,
            operator,
        )
    }

    fn lower_call(&mut self, node: &Node<'_>, call: &ruby_prism::CallNode<'_>) -> ExprId {
        self.lowered_call_spans
            .insert((self.span(node).start as usize, self.span(node).end as usize));
        let name = prism::constant_name(call.name());
        let raw_arguments = call.arguments().map_or_else(Vec::new, |arguments| {
            arguments.arguments().into_iter().collect()
        });
        if call.is_attribute_write() {
            if let Some(value) = raw_arguments.last() {
                let target_span = self.call_assignment_target_span(call, value);
                let receiver = call.receiver();
                if name == "[]=" && raw_arguments.len() >= 2 {
                    let arguments = raw_arguments[..raw_arguments.len() - 1]
                        .iter()
                        .flat_map(|argument| self.lower_argument(argument))
                        .collect();
                    let receiver = receiver
                        .map(|receiver| self.lower_node(&receiver))
                        .unwrap_or_else(|| self.push_expr(node, ExprKind::Read(Read::SelfValue)));
                    return self.lower_assignment_with_target_span(
                        node,
                        AssignTarget::Index {
                            receiver,
                            arguments,
                        },
                        target_span,
                        value,
                        AssignOperator::Set,
                    );
                }
                let receiver = receiver
                    .map(|receiver| self.lower_node(&receiver))
                    .unwrap_or_else(|| self.push_expr(node, ExprKind::Read(Read::SelfValue)));
                return self.lower_assignment_with_target_span(
                    node,
                    AssignTarget::Attribute {
                        receiver,
                        name: Name::new(name.trim_end_matches('=')),
                    },
                    target_span,
                    value,
                    AssignOperator::Set,
                );
            }
        }
        let receiver = call.receiver().map_or(Receiver::Implicit, |receiver| {
            Receiver::Explicit(self.lower_node(&receiver))
        });
        let mut arguments = Vec::new();
        let mut argument_groups = Vec::with_capacity(raw_arguments.len());
        let mut argument_spans = Vec::with_capacity(raw_arguments.len());
        for argument in &raw_arguments {
            arguments.extend(self.lower_argument(argument));
            argument_groups.push(arguments.len());
            argument_spans.push(self.span(argument));
        }
        let block = self.lower_block_argument(call.block());
        self.lower_call_parts(
            node,
            receiver,
            Name::new(name),
            arguments,
            argument_groups,
            argument_spans,
            block,
            call.is_safe_navigation(),
        )
    }

    fn call_assignment_target_span(
        &self,
        call: &ruby_prism::CallNode<'_>,
        value: &Node<'_>,
    ) -> Span {
        let start = call.receiver().map_or_else(
            || call.location().start_offset(),
            |receiver| receiver.location().start_offset(),
        );
        let mut end = value.location().start_offset().min(self.source.len());
        while end > start && self.source[end - 1].is_ascii_whitespace() {
            end -= 1;
        }
        if end > start && self.source[end - 1] == b'=' {
            end -= 1;
            while end > start && self.source[end - 1].is_ascii_whitespace() {
                end -= 1;
            }
        }
        self.span_offsets(start, end)
    }

    fn lower_special_call(
        &mut self,
        node: &Node<'_>,
        receiver: Receiver,
        name: &str,
        arguments: Option<ArgumentsNode<'_>>,
        block: Option<Node<'_>>,
        safe_navigation: bool,
    ) -> ExprId {
        let span = self.span(node);
        self.lowered_call_spans
            .insert((span.start as usize, span.end as usize));
        let raw_arguments = arguments.map_or_else(Vec::new, |arguments| {
            arguments.arguments().into_iter().collect::<Vec<_>>()
        });
        let mut lowered_arguments = Vec::new();
        let mut argument_groups = Vec::with_capacity(raw_arguments.len());
        let mut argument_spans = Vec::with_capacity(raw_arguments.len());
        for argument in &raw_arguments {
            lowered_arguments.extend(self.lower_argument(argument));
            argument_groups.push(lowered_arguments.len());
            argument_spans.push(self.span(argument));
        }
        let block = self.lower_block_argument(block);
        self.lower_call_parts(
            node,
            receiver,
            Name::new(name),
            lowered_arguments,
            argument_groups,
            argument_spans,
            block,
            safe_navigation,
        )
    }

    fn lower_call_parts(
        &mut self,
        node: &Node<'_>,
        receiver: Receiver,
        name: Name,
        arguments: Vec<Argument>,
        argument_groups: Vec<usize>,
        argument_spans: Vec<Span>,
        block: Option<super::BlockArgument>,
        safe_navigation: bool,
    ) -> ExprId {
        let span = self.span(node);
        self.lowered_call_spans
            .insert((span.start as usize, span.end as usize));
        self.push_expr(
            node,
            ExprKind::Call(super::Call {
                receiver,
                name,
                arguments,
                argument_groups,
                argument_spans,
                block,
                safe_navigation,
                span,
            }),
        )
    }

    fn lower_arguments(&mut self, arguments: Option<ArgumentsNode<'_>>) -> Vec<Argument> {
        arguments.map_or_else(Vec::new, |arguments| {
            arguments
                .arguments()
                .into_iter()
                .flat_map(|argument| self.lower_argument(&argument))
                .collect()
        })
    }

    fn lower_argument(&mut self, argument: &Node<'_>) -> Vec<Argument> {
        if argument.as_forwarding_arguments_node().is_some() {
            return vec![Argument::Forwarded];
        }
        if let Some(splat) = argument.as_splat_node() {
            return splat
                .expression()
                .map(|value| vec![Argument::Splat(self.lower_node(&value))])
                .unwrap_or_else(|| vec![Argument::Forwarded]);
        }
        if let Some(keyword_hash) = argument.as_keyword_hash_node() {
            let mut result = Vec::new();
            for child in &keyword_hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    if let Some(symbol) = assoc.key().as_symbol_node() {
                        result.push(Argument::Keyword {
                            name: Name::new(
                                String::from_utf8_lossy(symbol.unescaped()).into_owned(),
                            ),
                            name_span: self.span(&assoc.key()),
                            value: self.lower_node(&assoc.value()),
                        });
                    } else {
                        return vec![Argument::Positional(self.lower_node(argument))];
                    }
                } else if let Some(splat) = child.as_assoc_splat_node() {
                    if let Some(value) = splat.value() {
                        result.push(Argument::KeywordSplat(self.lower_node(&value)));
                    } else {
                        result.push(Argument::Forwarded);
                    }
                } else {
                    return vec![Argument::Positional(self.lower_node(argument))];
                }
            }
            return result;
        }
        vec![Argument::Positional(self.lower_node(argument))]
    }

    fn lower_block_argument(&mut self, block: Option<Node<'_>>) -> Option<super::BlockArgument> {
        let block = block?;
        if let Some(block_argument) = block.as_block_argument_node() {
            return block_argument
                .expression()
                .map(|expression| super::BlockArgument::Passed(self.lower_node(&expression)));
        }
        if block.as_block_node().is_some() {
            let closure = self.lower_closure(
                &block,
                block
                    .as_block_node()
                    .expect("checked block node")
                    .parameters(),
                block.as_block_node().expect("checked block node").body(),
                ClosureKind::Block,
            );
            return Some(super::BlockArgument::Inline(closure));
        }
        Some(super::BlockArgument::Passed(self.lower_node(&block)))
    }

    fn lower_hash(&mut self, node: &Node<'_>, elements: ruby_prism::NodeList<'_>) -> ExprId {
        let elements = elements
            .into_iter()
            .map(|child| {
                if let Some(assoc) = child.as_assoc_node() {
                    HashElement::Pair {
                        key: self.lower_node(&assoc.key()),
                        value: self.lower_node(&assoc.value()),
                    }
                } else if let Some(splat) = child.as_assoc_splat_node() {
                    if let Some(value) = splat.value() {
                        HashElement::Splat {
                            value: self.lower_node(&value),
                            span: self.span(&child),
                        }
                    } else {
                        HashElement::Splat {
                            value: self.lower_node(&child),
                            span: self.span(&child),
                        }
                    }
                } else {
                    HashElement::Splat {
                        value: self.lower_node(&child),
                        span: self.span(&child),
                    }
                }
            })
            .collect();
        self.push_expr(node, ExprKind::Hash(elements))
    }

    fn lower_control_arguments(&mut self, arguments: Option<ArgumentsNode<'_>>) -> Option<ExprId> {
        let arguments = arguments?.arguments().into_iter().collect::<Vec<_>>();
        match arguments.as_slice() {
            [] => None,
            [argument] => Some(self.lower_node(argument)),
            _ => {
                let expressions = arguments
                    .iter()
                    .map(|argument| self.lower_node(argument))
                    .collect();
                let span = self.span(&arguments[0]);
                Some(self.push_expr_with_span(span, ExprKind::Sequence(expressions)))
            }
        }
    }

    fn lower_closure(
        &mut self,
        node: &Node<'_>,
        parameters_node: Option<Node<'_>>,
        body_node: Option<Node<'_>>,
        kind: ClosureKind,
    ) -> ClosureId {
        let closure_id = ClosureId(self.program.closures.len() as u32);
        self.push_scope();
        let parameters = self.lower_parameters_from_node(parameters_node);
        let root = if let Some(body) = body_node {
            self.lower_node(&body)
        } else {
            self.nil(node)
        };
        let body_id = self.push_body(
            BodyOwner::Closure(closure_id),
            parameters.clone(),
            root,
            self.span(node),
        );
        let lexical_scope = self.current_scope();
        self.pop_scope();
        self.program.closures.push(Closure {
            body: body_id,
            parameters,
            span: self.span(node),
            lexical_scope,
            kind,
        });
        closure_id
    }

    fn lower_parameters_from_node(&mut self, node: Option<Node<'_>>) -> Parameters {
        let Some(node) = node else {
            return Parameters::default();
        };
        let parameters = node
            .as_block_parameters_node()
            .and_then(|block| block.parameters())
            .or_else(|| node.as_parameters_node());
        parameters.map_or_else(Parameters::default, |parameters| {
            self.lower_parameters(parameters)
        })
    }

    fn lower_parameters(&mut self, parameters: ParametersNode<'_>) -> Parameters {
        let mut result = Parameters {
            parameters: Vec::new(),
            forwarding: false,
            span: Some(self.span(&parameters.as_node())),
        };
        for parameter in &parameters.requireds() {
            self.push_parameter(&mut result, &parameter, ParameterKind::Required, true);
        }
        for parameter in &parameters.optionals() {
            self.push_parameter(&mut result, &parameter, ParameterKind::Optional, true);
        }
        if let Some(rest) = parameters.rest() {
            if rest.as_forwarding_parameter_node().is_some() {
                result.forwarding = true;
                self.push_parameter(&mut result, &rest, ParameterKind::Forwarded, false);
            } else {
                self.push_parameter(&mut result, &rest, ParameterKind::Rest, false);
            }
        }
        for parameter in &parameters.posts() {
            self.push_parameter(&mut result, &parameter, ParameterKind::Post, true);
        }
        for parameter in &parameters.keywords() {
            let kind = if parameter.as_required_keyword_parameter_node().is_some() {
                ParameterKind::RequiredKeyword
            } else {
                ParameterKind::OptionalKeyword
            };
            self.push_parameter(&mut result, &parameter, kind, true);
        }
        if let Some(rest) = parameters.keyword_rest() {
            if rest.as_forwarding_parameter_node().is_some() {
                result.forwarding = true;
                self.push_parameter(&mut result, &rest, ParameterKind::Forwarded, false);
            } else {
                self.push_parameter(&mut result, &rest, ParameterKind::KeywordRest, false);
            }
        }
        if let Some(block) = parameters.block() {
            let node = block.as_node();
            self.push_parameter(&mut result, &node, ParameterKind::Block, false);
        }
        result
    }

    fn push_parameter(
        &mut self,
        parameters: &mut Parameters,
        node: &Node<'_>,
        kind: ParameterKind,
        required_name: bool,
    ) {
        let name = node
            .as_required_parameter_node()
            .map(|parameter| prism::constant_name(parameter.name()))
            .or_else(|| {
                node.as_optional_parameter_node()
                    .map(|parameter| prism::constant_name(parameter.name()))
            })
            .or_else(|| {
                node.as_required_keyword_parameter_node()
                    .map(|parameter| prism::constant_name(parameter.name()))
            })
            .or_else(|| {
                node.as_optional_keyword_parameter_node()
                    .map(|parameter| prism::constant_name(parameter.name()))
            })
            .or_else(|| {
                node.as_rest_parameter_node()
                    .and_then(|parameter| parameter.name())
                    .map(prism::constant_name)
            })
            .or_else(|| {
                node.as_keyword_rest_parameter_node()
                    .and_then(|parameter| parameter.name())
                    .map(prism::constant_name)
            })
            .or_else(|| {
                node.as_block_parameter_node()
                    .and_then(|parameter| parameter.name())
                    .map(prism::constant_name)
            });
        let local = name
            .as_deref()
            .filter(|name| required_name || !name.is_empty())
            .map(|name| self.new_local(name));
        parameters.parameters.push(Parameter {
            local,
            name: name.map(Name::new),
            kind,
            span: self.span(node),
        });
    }

    fn lower_definition(
        &mut self,
        node: &Node<'_>,
        definition: &ruby_prism::DefNode<'_>,
    ) -> ExprId {
        let name = Name::new(prism::constant_name(definition.name()));
        let singleton = definition.receiver().is_some();
        self.push_scope();
        let parameters = definition
            .parameters()
            .map_or_else(Parameters::default, |parameters| {
                self.lower_parameters(parameters)
            });
        let root = if let Some(body) = definition.body() {
            self.lower_node(&body)
        } else {
            self.nil(node)
        };
        let body = self.push_body(
            BodyOwner::Method {
                name: name.clone(),
                singleton,
            },
            parameters,
            root,
            self.span(node),
        );
        self.pop_scope();
        let declaration = DeclId(self.program.declarations.len() as u32);
        self.program.declarations.push(Declaration {
            span: self.span(node),
            kind: DeclarationKind::Method {
                name,
                singleton,
                body,
            },
        });
        self.push_expr(node, ExprKind::Definition(declaration))
    }

    fn lower_class(&mut self, node: &Node<'_>, class: &ruby_prism::ClassNode<'_>) -> ExprId {
        let name = ConstantPath::new(self.text(&class.constant_path()));
        let body = class.body().map(|body| {
            self.push_scope();
            let root = self.lower_node(&body);
            let body_id = self.push_body(
                BodyOwner::Class(name.clone()),
                Parameters::default(),
                root,
                self.span(node),
            );
            self.pop_scope();
            body_id
        });
        let declaration = DeclId(self.program.declarations.len() as u32);
        self.program.declarations.push(Declaration {
            span: self.span(node),
            kind: DeclarationKind::Class { name, body },
        });
        self.push_expr(node, ExprKind::Definition(declaration))
    }

    fn lower_module(&mut self, node: &Node<'_>, module: &ruby_prism::ModuleNode<'_>) -> ExprId {
        let name = ConstantPath::new(self.text(&module.constant_path()));
        let body = module.body().map(|body| {
            self.push_scope();
            let root = self.lower_node(&body);
            let body_id = self.push_body(
                BodyOwner::Module(name.clone()),
                Parameters::default(),
                root,
                self.span(node),
            );
            self.pop_scope();
            body_id
        });
        let declaration = DeclId(self.program.declarations.len() as u32);
        self.program.declarations.push(Declaration {
            span: self.span(node),
            kind: DeclarationKind::Module { name, body },
        });
        self.push_expr(node, ExprKind::Definition(declaration))
    }

    fn lower_singleton_class(
        &mut self,
        node: &Node<'_>,
        singleton: &ruby_prism::SingletonClassNode<'_>,
    ) -> ExprId {
        let body = singleton.body().map(|body| {
            self.push_scope();
            let root = self.lower_node(&body);
            let body_id = self.push_body(
                BodyOwner::SingletonClass,
                Parameters::default(),
                root,
                self.span(node),
            );
            self.pop_scope();
            body_id
        });
        let declaration = DeclId(self.program.declarations.len() as u32);
        self.program.declarations.push(Declaration {
            span: self.span(node),
            kind: DeclarationKind::SingletonClass { body },
        });
        self.push_expr(node, ExprKind::Definition(declaration))
    }

    fn lower_begin(&mut self, node: &Node<'_>, begin: &ruby_prism::BeginNode<'_>) -> ExprId {
        let body = begin
            .statements()
            .map(|statements| self.lower_node(&statements.as_node()));
        let mut rescue = Vec::new();
        let mut next = begin.rescue_clause();
        while let Some(clause) = next {
            let exceptions = clause
                .exceptions()
                .into_iter()
                .map(|exception| self.lower_node(&exception))
                .collect();
            let reference = clause.reference().and_then(|reference| {
                reference
                    .as_local_variable_write_node()
                    .map(|write| self.local(&prism::constant_name(write.name())))
                    .or_else(|| {
                        reference
                            .as_local_variable_target_node()
                            .map(|target| self.local(&prism::constant_name(target.name())))
                    })
            });
            rescue.push(RescueClause {
                exceptions,
                reference,
                body: clause
                    .statements()
                    .map(|statements| self.lower_node(&statements.as_node())),
            });
            next = clause.subsequent();
        }
        let else_body = begin
            .else_clause()
            .and_then(|else_clause| else_clause.statements())
            .map(|statements| self.lower_node(&statements.as_node()));
        let ensure = begin
            .ensure_clause()
            .and_then(|ensure| ensure.statements())
            .map(|statements| self.lower_node(&statements.as_node()));
        self.push_expr(
            node,
            ExprKind::Begin(BeginExpr {
                body,
                rescue,
                else_body,
                ensure,
            }),
        )
    }
}

struct NestedExpressionLowerer<'lower, 'src> {
    lowerer: &'lower mut Lowerer<'src>,
    expressions: Vec<ExprId>,
}

impl<'pr, 'lower, 'src> Visit<'pr> for NestedExpressionLowerer<'lower, 'src> {
    fn visit_branch_node_enter(&mut self, node: Node<'pr>) {
        if Lowerer::is_assignment_node(&node) || Lowerer::is_special_call_node(&node) {
            let span = node.location();
            let key = (span.start_offset(), span.end_offset());
            let should_lower = if Lowerer::is_assignment_node(&node) {
                self.lowerer.lowered_assignment_spans.insert(key)
            } else {
                self.lowerer.lowered_call_spans.insert(key)
            };
            if should_lower {
                let expression = self.lowerer.lower_node(&node);
                self.expressions.push(expression);
            }
        }
    }

    fn visit_call_node(&mut self, node: &CallNode<'pr>) {
        let span = node.location();
        let key = (span.start_offset(), span.end_offset());
        if self.lowerer.lowered_call_spans.insert(key) {
            let expression = self.lowerer.lower_call(&node.as_node(), node);
            self.expressions.push(expression);
        }
        ruby_prism::visit_call_node(self, node);
    }
}
