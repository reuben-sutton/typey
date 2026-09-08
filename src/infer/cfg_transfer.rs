use super::{
    ivar_refinement_key, Analyzer, CallArguments, CallSite, Environment, Eval, Flow, FlowKind,
    HirCallView, KeywordArgument, MethodKey, OutcomeTypes, SharedKey, Strictness,
};
use crate::cfg;
use crate::hir::{self, ArrayElement, ExprKind, HashElement, Literal, Read};
use crate::prism;
use crate::types::Type;
use ruby_prism::{IfNode, Node, Visit};
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

/// The inference-side state at a CFG block boundary.
///
/// CFG construction remains type-free. This state is the first boundary where
/// value IDs, environments, and abrupt flow outcomes become abstract facts
/// that can be joined by the generic CFG worklist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BlockState {
    values: Vec<Option<Type>>,
    environment: Environment,
    flow: Flow,
}

impl BlockState {
    fn with_values(environment: Environment, values: Vec<Option<Type>>, flow: Flow) -> Self {
        Self {
            values,
            environment,
            flow,
        }
    }

    fn join(&self, other: &Self) -> Self {
        let environment = match (
            self.flow.contains(FlowKind::Normal),
            other.flow.contains(FlowKind::Normal),
        ) {
            (true, false) => self.environment.clone(),
            (false, true) => other.environment.clone(),
            _ => self.environment.join(&other.environment),
        };
        let values = (0..self.values.len().max(other.values.len()))
            .map(
                |index| match (self.values.get(index), other.values.get(index)) {
                    (Some(Some(left)), Some(Some(right))) => Some(left.join(right)),
                    _ => None,
                },
            )
            .collect();
        Self {
            values,
            environment,
            flow: self.flow.union(other.flow),
        }
    }

    fn value(&self, id: cfg::ValueId) -> Option<Type> {
        self.values.get(id.0 as usize).cloned().flatten()
    }

    fn set_value(&mut self, id: cfg::ValueId, type_: Type) {
        let index = id.0 as usize;
        if self.values.len() <= index {
            self.values.resize(index + 1, None);
        }
        self.values[index] = Some(type_);
    }
}

#[derive(Default)]
struct SpanNodeIndex<'node> {
    nodes: HashMap<(usize, usize), Node<'node>>,
}

impl<'node> Visit<'node> for SpanNodeIndex<'node> {
    fn visit_branch_node_enter(&mut self, node: Node<'node>) {
        let span = prism::span(&node);
        self.nodes.entry(span).or_insert(node);
    }

    fn visit_leaf_node_enter(&mut self, node: Node<'node>) {
        let span = prism::span(&node);
        self.nodes.entry(span).or_insert(node);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BodyContext {
    body: hir::BodyId,
    method: Option<MethodKey>,
    self_type: Type,
    parameters: hir::Parameters,
    strictness: Strictness,
}

struct BodyTransfer<'analyzer, 'src, 'node> {
    analyzer: &'analyzer mut Analyzer<'src>,
    context: BodyContext,
    nodes: &'node SpanNodeIndex<'node>,
    fixed_array_elements: HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    normal_type: Type,
    abrupt: OutcomeTypes,
    terminal_flow: Flow,
    final_environment: Option<Environment>,
}

fn body_can_transfer(program: &hir::Program, body: hir::BodyId) -> bool {
    let Some(body) = program.body(body) else {
        return false;
    };
    let mut visiting = HashSet::new();
    expr_can_transfer(program, body.root, &mut visiting)
}

fn expr_can_transfer(
    program: &hir::Program,
    expression: hir::ExprId,
    visiting: &mut HashSet<hir::ExprId>,
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
            !call.safe_navigation
                && call.block.is_none()
                && match &call.receiver {
                    hir::Receiver::Implicit | hir::Receiver::Explicit(_) => true,
                    hir::Receiver::Super | hir::Receiver::Yield => false,
                }
                && match &call.receiver {
                    hir::Receiver::Explicit(receiver) => {
                        expr_can_transfer(program, *receiver, visiting)
                    }
                    _ => true,
                }
                && call.arguments.iter().all(|argument| match argument {
                    hir::Argument::Positional(value) | hir::Argument::Splat(value) => {
                        expr_can_transfer(program, *value, visiting)
                    }
                    hir::Argument::Keyword { value, .. } => {
                        expr_can_transfer(program, *value, visiting)
                    }
                    hir::Argument::KeywordSplat(_) | hir::Argument::Forwarded => false,
                })
        }
        ExprKind::Array(elements) => elements.iter().all(|element| {
            match element {
                ArrayElement::Value(value) => expr_can_transfer(program, *value, visiting),
                // The splat wrapper has its own source span and is not yet
                // represented by an owned CFG operand.
                ArrayElement::Splat(_) => false,
            }
        }),
        ExprKind::Hash(elements) => elements.iter().all(|element| match element {
            HashElement::Pair { key, value } => {
                expr_can_transfer(program, *key, visiting)
                    && expr_can_transfer(program, *value, visiting)
            }
            // See the array-splat boundary above.
            HashElement::Splat(_) => false,
        }),
        ExprKind::Assign {
            target,
            value,
            operator,
            ..
        } => {
            let direct_target = matches!(
                target,
                hir::AssignTarget::Local(_)
                    | hir::AssignTarget::InstanceVariable(_)
                    | hir::AssignTarget::ClassVariable(_)
                    | hir::AssignTarget::Global(_)
                    | hir::AssignTarget::Constant(_)
            );
            let logical_target = matches!(target, hir::AssignTarget::Local(_));
            let target_supported = match target {
                hir::AssignTarget::Local(_)
                | hir::AssignTarget::InstanceVariable(_)
                | hir::AssignTarget::ClassVariable(_)
                | hir::AssignTarget::Global(_)
                | hir::AssignTarget::Constant(_) => direct_target,
                hir::AssignTarget::Attribute { receiver, .. } => {
                    expr_can_transfer(program, *receiver, visiting)
                }
                hir::AssignTarget::Index {
                    receiver,
                    arguments,
                } => {
                    expr_can_transfer(program, *receiver, visiting)
                        && arguments.iter().all(|argument| match argument {
                            hir::Argument::Positional(value) => {
                                expr_can_transfer(program, *value, visiting)
                            }
                            hir::Argument::Splat(_)
                            | hir::Argument::Keyword { .. }
                            | hir::Argument::KeywordSplat(_)
                            | hir::Argument::Forwarded => false,
                        })
                }
            };
            matches!(
                (operator, target_supported),
                (
                    hir::AssignOperator::Set | hir::AssignOperator::Binary(_),
                    true
                ) | (hir::AssignOperator::And | hir::AssignOperator::Or, true)
            ) && (logical_target
                || matches!(
                    operator,
                    hir::AssignOperator::Set | hir::AssignOperator::Binary(_)
                ))
                && expr_can_transfer(program, *value, visiting)
        }
        ExprKind::Sequence(expressions) => expressions
            .iter()
            .all(|expression| expr_can_transfer(program, *expression, visiting)),
        ExprKind::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_can_transfer(program, *condition, visiting)
                && expr_can_transfer(program, *then_body, visiting)
                && else_body.is_none_or(|else_body| expr_can_transfer(program, else_body, visiting))
        }
        _ => false,
    };
    visiting.remove(&expression);
    supported
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ConditionalState {
    block: BlockState,
    result: Eval,
    path_reachable: bool,
}

struct ConditionalTransfer<'analyzer, 'src, 'node, 'nodes> {
    analyzer: &'analyzer mut Analyzer<'src>,
    predicate: &'nodes Node<'node>,
    then_node: Option<&'nodes Node<'node>>,
    subsequent: Option<&'nodes Node<'node>>,
    then_first: Option<&'nodes Node<'node>>,
    else_first: Option<&'nodes Node<'node>>,
    then_reachable: bool,
    else_reachable: bool,
    report_unreachable: bool,
}

struct LoopTransfer<'analyzer, 'src, 'node, 'nodes> {
    analyzer: &'analyzer mut Analyzer<'src>,
    predicate: &'nodes Node<'node>,
    statements: Option<&'nodes ruby_prism::StatementsNode<'node>>,
    predicate_truthy: bool,
    abrupt: OutcomeTypes,
    break_type: Type,
    terminal_flow: Flow,
}

struct ForTransfer<'analyzer, 'src, 'node, 'nodes> {
    analyzer: &'analyzer mut Analyzer<'src>,
    index: &'nodes Node<'node>,
    statements: Option<&'nodes ruby_prism::StatementsNode<'node>>,
    element_type: Type,
    abrupt: OutcomeTypes,
    break_type: Type,
    terminal_flow: Flow,
}

fn conditional_graph() -> &'static cfg::Cfg {
    static GRAPH: OnceLock<cfg::Cfg> = OnceLock::new();
    GRAPH.get_or_init(|| cfg::Cfg {
        body: hir::BodyId(0),
        entry: cfg::BlockId(0),
        blocks: vec![
            cfg::BasicBlock {
                id: cfg::BlockId(0),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Branch {
                    condition: cfg::ValueId(0),
                    truthy: cfg::BlockId(1),
                    falsy: cfg::BlockId(2),
                },
                unwind: None,
            },
            cfg::BasicBlock {
                id: cfg::BlockId(1),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Jump {
                    target: cfg::BlockId(3),
                    arguments: Vec::new(),
                },
                unwind: None,
            },
            cfg::BasicBlock {
                id: cfg::BlockId(2),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Jump {
                    target: cfg::BlockId(3),
                    arguments: Vec::new(),
                },
                unwind: None,
            },
            cfg::BasicBlock {
                id: cfg::BlockId(3),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Return(None),
                unwind: None,
            },
        ],
        conditionals: Vec::new(),
        unsupported_spans: Vec::new(),
        expression_values: Vec::new(),
    })
}

fn loop_graph() -> &'static cfg::Cfg {
    static GRAPH: OnceLock<cfg::Cfg> = OnceLock::new();
    GRAPH.get_or_init(|| cfg::Cfg {
        body: hir::BodyId(0),
        entry: cfg::BlockId(0),
        blocks: vec![
            cfg::BasicBlock {
                id: cfg::BlockId(0),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Jump {
                    target: cfg::BlockId(1),
                    arguments: Vec::new(),
                },
                unwind: None,
            },
            cfg::BasicBlock {
                id: cfg::BlockId(1),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Branch {
                    condition: cfg::ValueId(0),
                    truthy: cfg::BlockId(2),
                    falsy: cfg::BlockId(3),
                },
                unwind: None,
            },
            cfg::BasicBlock {
                id: cfg::BlockId(2),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Jump {
                    target: cfg::BlockId(1),
                    arguments: Vec::new(),
                },
                unwind: None,
            },
            cfg::BasicBlock {
                id: cfg::BlockId(3),
                parameters: Vec::new(),
                operations: Vec::new(),
                terminator: cfg::Terminator::Return(None),
                unwind: None,
            },
        ],
        conditionals: Vec::new(),
        unsupported_spans: Vec::new(),
        expression_values: Vec::new(),
    })
}

impl<'analyzer, 'src, 'node> BodyTransfer<'analyzer, 'src, 'node> {
    fn transfer_write(
        analyzer: &mut Analyzer<'src>,
        node: &Node<'node>,
        place: &cfg::Place,
        actual: Type,
        environment: &mut Environment,
    ) -> Type {
        match place {
            cfg::Place::Local(local) => {
                let name = analyzer
                    .hir_program
                    .local_name(*local)
                    .map_or_else(String::new, |name| name.as_str().to_owned());
                let type_ =
                    analyzer.apply_inline_assertion_in_environment(node, actual, environment);
                environment.bind(name, type_.clone());
                type_
            }
            cfg::Place::InstanceVariable(name) => {
                let name = name.as_str().to_owned();
                let type_ =
                    analyzer.apply_inline_assertion_in_environment(node, actual, environment);
                analyzer.observe_ivar(environment, name.clone(), &type_, false);
                environment.bind(ivar_refinement_key(&name), type_.clone());
                type_
            }
            cfg::Place::ClassVariable(name) => {
                let type_ = analyzer.apply_inline_assertion(node, actual);
                analyzer.observe_class_var(environment, name.as_str().to_owned(), &type_);
                type_
            }
            cfg::Place::Global(name) => {
                let type_ = analyzer.apply_inline_assertion(node, actual);
                analyzer.observe_global(name.as_str().to_owned(), &type_);
                type_
            }
            cfg::Place::Constant(path) => {
                let type_ = analyzer.apply_inline_assertion(node, actual);
                analyzer.observe_constant(environment, path.as_str().to_owned(), &type_);
                type_
            }
        }
    }

    fn transfer_call(
        analyzer: &mut Analyzer<'src>,
        node: &Node<'node>,
        operation: &cfg::OperationKind,
        values: &[Option<Type>],
        fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let cfg::OperationKind::Call {
            receiver,
            name,
            arguments: operands,
            block,
            safe_navigation,
        } = operation
        else {
            return None;
        };
        if block.is_some() || *safe_navigation {
            return None;
        }
        let call = node.as_call_node()?;
        let raw_arguments = call
            .arguments()
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        let mut call_arguments = CallArguments::default();
        let mut operand_index = 0usize;
        for (argument_index, argument_node) in raw_arguments.into_iter().enumerate() {
            if let Some(keyword_hash) = argument_node.as_keyword_hash_node() {
                let elements = keyword_hash.elements().into_iter().collect::<Vec<_>>();
                let keyword_group = operands
                    .get(operand_index..operand_index.saturating_add(elements.len()))
                    .is_some_and(|group| {
                        group
                            .iter()
                            .all(|operand| matches!(operand, cfg::ArgumentOperand::Keyword { .. }))
                    });
                if keyword_group && !elements.is_empty() {
                    let mut key = Type::Never;
                    let mut value = Type::Never;
                    let mut keyword_arguments = Vec::with_capacity(elements.len());
                    for element in elements {
                        let assoc = element.as_assoc_node()?;
                        let cfg::ArgumentOperand::Keyword {
                            name,
                            value: value_id,
                        } = operands.get(operand_index)?
                        else {
                            return None;
                        };
                        let type_ = values.get(value_id.0 as usize).cloned().flatten()?;
                        let name = name.as_str().to_owned();
                        key = key.join(&Type::Symbol);
                        value = value.join(&type_);
                        analyzer.record(&assoc.key(), Type::Symbol);
                        keyword_arguments.push(KeywordArgument {
                            name,
                            node: assoc.value(),
                            type_,
                        });
                        operand_index += 1;
                    }
                    let key = if key.is_never() { Type::Any } else { key };
                    let value = if value.is_never() { Type::Any } else { value };
                    let hash_type = analyzer.apply_inline_assertion(
                        &argument_node,
                        Type::Hash(Box::new(key), Box::new(value)),
                    );
                    analyzer.record(&argument_node, hash_type.clone());
                    call_arguments.argument_nodes.push(argument_node);
                    call_arguments.argument_types.push(hash_type.clone());
                    call_arguments.argument_indices.push(argument_index);
                    call_arguments.keyword_arguments.extend(keyword_arguments);
                    continue;
                }
            }
            if let Some(cfg::ArgumentOperand::Splat(value)) = operands.get(operand_index) {
                let type_ = values.get(value.0 as usize).cloned().flatten()?;
                if let Some(elements) = fixed_array_elements.get(value) {
                    for element in elements {
                        let type_ = values.get(element.0 as usize).cloned().flatten()?;
                        call_arguments.argument_types.push(type_.clone());
                        call_arguments.argument_indices.push(argument_index);
                        call_arguments.positional_indices.push(argument_index);
                        call_arguments.positional_types.push(type_);
                    }
                } else if let Type::Tuple(elements) = type_ {
                    for type_ in elements {
                        call_arguments.argument_types.push(type_.clone());
                        call_arguments.argument_indices.push(argument_index);
                        call_arguments.positional_indices.push(argument_index);
                        call_arguments.positional_types.push(type_);
                    }
                } else if type_.is_any() {
                    call_arguments.has_unknown_positional_splat = true;
                } else {
                    call_arguments.has_dynamic_positional_splat = true;
                    call_arguments.dynamic_positional_splat_types.push(type_);
                }
                call_arguments.argument_nodes.push(argument_node);
                operand_index += 1;
                continue;
            }
            let Some(cfg::ArgumentOperand::Positional(value)) = operands.get(operand_index) else {
                return None;
            };
            let type_ = values.get(value.0 as usize).cloned().flatten()?;
            call_arguments.argument_nodes.push(argument_node);
            call_arguments.argument_types.push(type_.clone());
            call_arguments.argument_indices.push(argument_index);
            call_arguments.positional_indices.push(argument_index);
            call_arguments.positional_types.push(type_);
            operand_index += 1;
        }
        if operand_index != operands.len() {
            return None;
        }

        let receiver_node = call.receiver();
        let receiver_type = match receiver {
            cfg::ReceiverOperand::Implicit => environment.self_type.clone(),
            cfg::ReceiverOperand::Value(value) => {
                values.get(value.0 as usize).cloned().flatten()?
            }
            cfg::ReceiverOperand::Super | cfg::ReceiverOperand::Yield => return None,
        };
        let site = CallSite {
            argument_nodes: &call_arguments.argument_nodes,
            argument_types: &call_arguments.argument_types,
            block: None,
        };
        let type_ = if matches!(receiver, cfg::ReceiverOperand::Implicit) {
            let key = analyzer.implicit_method_key(name.as_str(), environment);
            analyzer.record_method_dependency(&key, environment);
            if let Some(signature) = analyzer
                .observe_call(&key, &call_arguments, false)
                .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
            {
                analyzer.invoke_signature(
                    node,
                    name.as_str(),
                    &signature,
                    &call_arguments,
                    Some(&receiver_type),
                    None,
                )
            } else {
                analyzer.eval_global_call(
                    node,
                    name.as_str(),
                    &call_arguments.argument_nodes,
                    &call_arguments.argument_types,
                    None,
                    environment,
                )
            }
        } else {
            let dispatch_receiver = receiver_type.clone();
            let key = analyzer.receiver_method_key(
                receiver_node.as_ref(),
                &dispatch_receiver,
                name.as_str(),
                environment,
            );
            if let Some(key) = key {
                analyzer.record_method_dependency(&key, environment);
                if let Some(signature) = analyzer
                    .observe_call(&key, &call_arguments, false)
                    .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
                {
                    let type_ = analyzer.invoke_signature(
                        node,
                        name.as_str(),
                        &signature,
                        &call_arguments,
                        Some(&dispatch_receiver),
                        None,
                    );
                    if name.as_str() == "new"
                        && Analyzer::class_object_instance_type(&dispatch_receiver).is_some()
                    {
                        analyzer.instantiate_generic_class(type_)
                    } else {
                        type_
                    }
                } else {
                    analyzer.eval_method_call(&dispatch_receiver, name.as_str(), &site, environment)
                }
            } else {
                analyzer.eval_method_call(&dispatch_receiver, name.as_str(), &site, environment)
            }
        };
        let mut result = if type_.is_never() {
            Eval::raised(type_)
        } else {
            Eval::value(type_)
        };
        let type_ =
            analyzer.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
        if result.normal_type.is_some() {
            result.normal_type = Some(type_.clone());
        }
        result.type_ = type_;
        Some(result)
    }

    fn transfer_array(
        analyzer: &mut Analyzer<'src>,
        node: &Node<'node>,
        elements: &[cfg::ArrayOperand],
        values: &[Option<Type>],
        preserve_fixed_shape: bool,
        environment: &mut Environment,
    ) -> Option<Type> {
        let mut element_types = Vec::with_capacity(elements.len());
        let mut fixed_length = true;
        let mut element = Type::Never;
        for operand in elements {
            let (value, splat) = match operand {
                cfg::ArrayOperand::Value(value) => (value, false),
                cfg::ArrayOperand::Splat(value) => (value, true),
            };
            let type_ = values.get(value.0 as usize).cloned().flatten()?;
            let type_ = if splat {
                fixed_length = false;
                analyzer.array_element_type(&type_)
            } else {
                type_
            };
            element_types.push(type_.clone());
            element = element.join(&type_);
        }
        let element = if element.is_never() {
            if analyzer.preserve_literal_tuples {
                Type::Never
            } else {
                Type::Any
            }
        } else {
            element
        };
        let inferred = if fixed_length
            && (preserve_fixed_shape
                || (analyzer.preserve_literal_tuples && analyzer.literal_tuple_depth == 0))
        {
            Type::Tuple(element_types)
        } else {
            Type::Array(Box::new(element))
        };
        Some(analyzer.apply_inline_assertion_in_environment(node, inferred, environment))
    }

    fn transfer_hash(
        analyzer: &mut Analyzer<'src>,
        node: &Node<'node>,
        elements: &[cfg::HashOperand],
        values: &[Option<Type>],
        environment: &mut Environment,
    ) -> Option<Type> {
        let mut key = Type::Never;
        let mut value = Type::Never;
        for element in elements {
            match element {
                cfg::HashOperand::Pair {
                    key: key_id,
                    value: value_id,
                } => {
                    key = key.join(&values.get(key_id.0 as usize).cloned().flatten()?);
                    value = value.join(&values.get(value_id.0 as usize).cloned().flatten()?);
                }
                cfg::HashOperand::Splat(value_id) => {
                    match values.get(value_id.0 as usize).cloned().flatten()? {
                        Type::Hash(splat_key, splat_value) => {
                            key = key.join(&splat_key);
                            value = value.join(&splat_value);
                        }
                        Type::Any => {
                            key = Type::Any;
                            value = Type::Any;
                        }
                        _ => {}
                    }
                }
            }
        }
        let key = if key.is_never() { Type::Any } else { key };
        let value = if value.is_never() { Type::Any } else { value };
        Some(analyzer.apply_inline_assertion_in_environment(
            node,
            Type::Hash(Box::new(key), Box::new(value)),
            environment,
        ))
    }

    fn pattern_reachability(pattern: &cfg::Pattern, source: &Type) -> Option<(bool, bool, Type)> {
        let (truthy, falsy) = match pattern {
            cfg::Pattern::Truthy => (
                !source.truthy_part().is_never(),
                !source.falsy_part().is_never(),
            ),
            cfg::Pattern::Nil => (
                !source.meet(&Type::Nil).is_never(),
                !source.without(&Type::Nil).is_never(),
            ),
            cfg::Pattern::Case { .. } => return None,
        };
        let test_type = match (truthy, falsy) {
            (true, true) => Type::union([Type::True, Type::False]),
            (true, false) => Type::True,
            (false, true) => Type::False,
            (false, false) => Type::Never,
        };
        Some((truthy, falsy, test_type))
    }

    fn truthiness_reachability(source: &Type) -> (bool, bool) {
        (
            !source.truthy_part().is_never(),
            !source.falsy_part().is_never(),
        )
    }

    fn narrow_conditional_branch(
        &mut self,
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
        let Some(expression) = self.analyzer.hir_program.expression(conditional.condition) else {
            return;
        };
        let span = (expression.span.start as usize, expression.span.end as usize);
        let Some(node) = self.nodes.nodes.get(&span) else {
            return;
        };
        self.analyzer
            .narrow_from_predicate(node, environment, truthy);
    }
}

impl<'analyzer, 'src, 'node> cfg::transfer::BlockTransfer for BodyTransfer<'analyzer, 'src, 'node> {
    type State = BlockState;
    type Error = ();

    fn transfer_block(
        &mut self,
        graph: &cfg::Cfg,
        block: &cfg::BasicBlock,
        state: &Self::State,
    ) -> Result<Vec<cfg::transfer::TransferEdge<Self::State>>, Self::Error> {
        debug_assert_eq!(graph.body, self.context.body);
        let _strictness = self.context.strictness;
        let mut next = state.clone();
        let nodes = self.nodes;
        for operation in &block.operations {
            let node = nodes
                .nodes
                .get(&(operation.span.start as usize, operation.span.end as usize))
                .ok_or(())?;
            let type_ = match &operation.kind {
                cfg::OperationKind::Const { value } => Analyzer::cfg_literal_type(value),
                cfg::OperationKind::Read { place } => {
                    let read = match place {
                        cfg::Place::Local(local) => Read::Local(*local),
                        cfg::Place::InstanceVariable(name) => Read::InstanceVariable(name.clone()),
                        cfg::Place::ClassVariable(name) => Read::ClassVariable(name.clone()),
                        cfg::Place::Global(name) => Read::Global(name.clone()),
                        cfg::Place::Constant(path) => Read::Constant(path.clone()),
                    };
                    self.analyzer
                        .transfer_cfg_read(node, read, &mut next.environment)
                }
                cfg::OperationKind::ReadSpecial { read } => {
                    self.analyzer
                        .transfer_cfg_read(node, read.clone(), &mut next.environment)
                }
                cfg::OperationKind::Write { place, value } => {
                    let actual = next.value(*value).ok_or(())?;
                    Self::transfer_write(self.analyzer, node, place, actual, &mut next.environment)
                }
                cfg::OperationKind::Call { .. } => {
                    let result = Self::transfer_call(
                        self.analyzer,
                        node,
                        &operation.kind,
                        &next.values,
                        &self.fixed_array_elements,
                        &mut next.environment,
                    )
                    .ok_or(())?;
                    self.abrupt = self.abrupt.join(&result.abrupt);
                    if !result.flow.contains(FlowKind::Normal) {
                        self.analyzer.record(node, result.type_.clone());
                        return Ok(Vec::new());
                    }
                    next.flow = next.flow.union(result.flow.without(FlowKind::Normal));
                    result.normal_type.ok_or(())?
                }
                cfg::OperationKind::BuildArray { elements } => Self::transfer_array(
                    self.analyzer,
                    node,
                    elements,
                    &next.values,
                    operation
                        .result
                        .is_some_and(|result| self.fixed_array_elements.contains_key(&result)),
                    &mut next.environment,
                )
                .ok_or(())?,
                cfg::OperationKind::BuildHash { elements } => Self::transfer_hash(
                    self.analyzer,
                    node,
                    elements,
                    &next.values,
                    &mut next.environment,
                )
                .ok_or(())?,
                cfg::OperationKind::PatternTest { value, pattern } => {
                    let source = next.value(*value).ok_or(())?;
                    let (_, _, type_) = Self::pattern_reachability(pattern, &source).ok_or(())?;
                    type_
                }
                _ => return Err(()),
            };
            if let Some(result) = operation.result {
                next.set_value(result, type_.clone());
            }
            if !matches!(operation.kind, cfg::OperationKind::PatternTest { .. }) {
                self.analyzer.record(node, type_);
            }
        }

        let edge = |target, state| cfg::transfer::TransferEdge { target, state };
        match &block.terminator {
            cfg::Terminator::Jump { target, arguments } => {
                let target_block = graph.block(*target).ok_or(())?;
                for (parameter, argument) in target_block.parameters.iter().zip(arguments) {
                    let type_ = next.value(*argument).ok_or(())?;
                    next.set_value(parameter.value, type_);
                }
                Ok(vec![edge(*target, next)])
            }
            cfg::Terminator::Return(value) => {
                self.normal_type = value
                    .and_then(|value| next.value(value))
                    .unwrap_or(Type::Nil);
                self.final_environment = Some(next.environment);
                self.terminal_flow = self.terminal_flow.union(next.flow);
                Ok(Vec::new())
            }
            cfg::Terminator::Unreachable => Ok(Vec::new()),
            cfg::Terminator::Branch {
                condition,
                truthy,
                falsy,
            } => {
                let pattern =
                    block
                        .operations
                        .iter()
                        .find_map(|operation| match operation.result {
                            Some(result) if result == *condition => {
                                if let cfg::OperationKind::PatternTest { value, pattern } =
                                    &operation.kind
                                {
                                    Some((Some(*value), Some(pattern)))
                                } else {
                                    Some((None, None))
                                }
                            }
                            _ => None,
                        });
                let (source_id, pattern) = pattern.unwrap_or((None, None));
                let source = next.value(source_id.unwrap_or(*condition)).ok_or(())?;
                let (truthy_reachable, falsy_reachable) = if let Some(pattern) = pattern {
                    let (truthy, falsy, _) =
                        Self::pattern_reachability(pattern, &source).ok_or(())?;
                    (truthy, falsy)
                } else {
                    Self::truthiness_reachability(&source)
                };
                let mut edges = Vec::with_capacity(2);
                if truthy_reachable {
                    let mut state = next.clone();
                    if pattern.is_none() {
                        self.narrow_conditional_branch(
                            graph,
                            *truthy,
                            true,
                            &mut state.environment,
                        );
                    }
                    edges.push(edge(*truthy, state));
                }
                if falsy_reachable {
                    let mut state = next;
                    if pattern.is_none() {
                        self.narrow_conditional_branch(
                            graph,
                            *falsy,
                            false,
                            &mut state.environment,
                        );
                    }
                    edges.push(edge(*falsy, state));
                }
                Ok(edges)
            }
            cfg::Terminator::Raise(_) => Err(()),
        }
    }

    fn join_state(
        &mut self,
        current: Option<&Self::State>,
        incoming: Self::State,
    ) -> (Self::State, bool) {
        let Some(current) = current else {
            return (incoming, true);
        };
        let joined = current.join(&incoming);
        let changed = joined != *current;
        (joined, changed)
    }
}

impl<'analyzer, 'src, 'node, 'nodes> cfg::transfer::BlockTransfer
    for ConditionalTransfer<'analyzer, 'src, 'node, 'nodes>
{
    type State = ConditionalState;
    type Error = ();

    fn transfer_block(
        &mut self,
        _cfg: &cfg::Cfg,
        block: &cfg::BasicBlock,
        state: &Self::State,
    ) -> Result<Vec<cfg::transfer::TransferEdge<Self::State>>, Self::Error> {
        let edge = |target, state| cfg::transfer::TransferEdge { target, state };
        Ok(match block.id {
            cfg::BlockId(0) => {
                let mut then_environment = state.block.environment.clone();
                self.analyzer
                    .narrow_from_predicate(&self.predicate, &mut then_environment, true);
                let mut else_environment = state.block.environment.clone();
                self.analyzer
                    .narrow_from_predicate(&self.predicate, &mut else_environment, false);
                vec![
                    edge(
                        cfg::BlockId(1),
                        ConditionalState {
                            block: BlockState::with_values(
                                then_environment,
                                Vec::new(),
                                Flow::normal(),
                            ),
                            result: Eval::unreachable(),
                            path_reachable: self.then_reachable,
                        },
                    ),
                    edge(
                        cfg::BlockId(2),
                        ConditionalState {
                            block: BlockState::with_values(
                                else_environment,
                                Vec::new(),
                                Flow::normal(),
                            ),
                            result: Eval::unreachable(),
                            path_reachable: self.else_reachable,
                        },
                    ),
                ]
            }
            cfg::BlockId(1) => {
                if !state.path_reachable && self.report_unreachable {
                    if let Some(first) = self.then_first {
                        self.analyzer.error(first, "This code is unreachable");
                    }
                }
                let mut environment = state.block.environment.clone();
                let result = self.then_node.map_or_else(
                    || Eval::value(Type::Nil),
                    |then_node| self.analyzer.eval_node(then_node, &mut environment),
                );
                let result = if state.path_reachable {
                    result
                } else {
                    Eval::unreachable()
                };
                vec![edge(
                    cfg::BlockId(3),
                    ConditionalState {
                        block: BlockState::with_values(environment, Vec::new(), result.flow),
                        result,
                        path_reachable: state.path_reachable,
                    },
                )]
            }
            cfg::BlockId(2) => {
                if !state.path_reachable && self.report_unreachable {
                    if let Some(first) = self.else_first {
                        self.analyzer.error(first, "This code is unreachable");
                    }
                }
                let mut environment = state.block.environment.clone();
                let result = self.subsequent.map_or_else(
                    || Eval::value(Type::Nil),
                    |subsequent| self.analyzer.eval_alternative(subsequent, &mut environment),
                );
                let result = if state.path_reachable {
                    result
                } else {
                    Eval::unreachable()
                };
                vec![edge(
                    cfg::BlockId(3),
                    ConditionalState {
                        block: BlockState::with_values(environment, Vec::new(), result.flow),
                        result,
                        path_reachable: state.path_reachable,
                    },
                )]
            }
            cfg::BlockId(3) => Vec::new(),
            _ => Vec::new(),
        })
    }

    fn join_state(
        &mut self,
        current: Option<&Self::State>,
        incoming: Self::State,
    ) -> (Self::State, bool) {
        let Some(current) = current else {
            return (incoming, true);
        };
        let joined = Self::State {
            block: current.block.join(&incoming.block),
            result: Eval::combine(&current.result, &incoming.result),
            path_reachable: current.path_reachable || incoming.path_reachable,
        };
        let changed = joined != *current;
        (joined, changed)
    }
}

impl<'analyzer, 'src, 'node, 'nodes> cfg::transfer::BlockTransfer
    for LoopTransfer<'analyzer, 'src, 'node, 'nodes>
{
    type State = BlockState;
    type Error = ();

    fn transfer_block(
        &mut self,
        _cfg: &cfg::Cfg,
        block: &cfg::BasicBlock,
        state: &Self::State,
    ) -> Result<Vec<cfg::transfer::TransferEdge<Self::State>>, Self::Error> {
        let edge = |target, state| cfg::transfer::TransferEdge { target, state };
        Ok(match block.id {
            cfg::BlockId(0) => vec![edge(cfg::BlockId(1), state.clone())],
            cfg::BlockId(1) => {
                let mut condition_environment = state.environment.clone();
                let condition_result = self
                    .analyzer
                    .eval_node(self.predicate, &mut condition_environment);
                self.abrupt = self.abrupt.join(
                    &condition_result
                        .abrupt
                        .without(FlowKind::Break)
                        .without(FlowKind::Next),
                );
                self.terminal_flow = self.terminal_flow.union(
                    condition_result
                        .flow
                        .without(FlowKind::Normal)
                        .without(FlowKind::Break)
                        .without(FlowKind::Next),
                );
                if !condition_result.flow.contains(FlowKind::Normal) {
                    Vec::new()
                } else {
                    let mut body_environment = condition_environment.clone();
                    self.analyzer.narrow_from_predicate(
                        self.predicate,
                        &mut body_environment,
                        self.predicate_truthy,
                    );
                    vec![
                        edge(
                            cfg::BlockId(3),
                            BlockState::with_values(
                                condition_environment,
                                Vec::new(),
                                Flow::normal(),
                            ),
                        ),
                        edge(
                            cfg::BlockId(2),
                            BlockState::with_values(body_environment, Vec::new(), Flow::normal()),
                        ),
                    ]
                }
            }
            cfg::BlockId(2) => {
                let mut body_environment = state.environment.clone();
                let body_result = self.statements.map_or_else(
                    || Eval::value(Type::Nil),
                    |statements| {
                        self.analyzer
                            .eval_statements(statements, &mut body_environment)
                    },
                );
                let body_terminal_flow = body_result
                    .flow
                    .without(FlowKind::Normal)
                    .without(FlowKind::Break)
                    .without(FlowKind::Next);
                self.terminal_flow = self.terminal_flow.union(body_terminal_flow);
                if !body_terminal_flow.is_empty() {
                    self.abrupt = self.abrupt.join(
                        &body_result
                            .abrupt
                            .without(FlowKind::Break)
                            .without(FlowKind::Next),
                    );
                }
                if body_result.flow.contains(FlowKind::Break) {
                    self.break_type = self.break_type.join(&body_result.abrupt.break_type);
                }
                let mut edges = Vec::new();
                if body_result.flow.contains(FlowKind::Break) {
                    edges.push(edge(
                        cfg::BlockId(3),
                        BlockState::with_values(
                            body_environment.clone(),
                            Vec::new(),
                            Flow::normal(),
                        ),
                    ));
                }
                if body_result.flow.contains(FlowKind::Normal)
                    || body_result.flow.contains(FlowKind::Next)
                {
                    edges.push(edge(
                        cfg::BlockId(1),
                        BlockState::with_values(body_environment, Vec::new(), Flow::normal()),
                    ));
                }
                edges
            }
            cfg::BlockId(3) => Vec::new(),
            _ => Vec::new(),
        })
    }

    fn join_state(
        &mut self,
        current: Option<&Self::State>,
        incoming: Self::State,
    ) -> (Self::State, bool) {
        let Some(current) = current else {
            return (incoming, true);
        };
        let joined = current.join(&incoming);
        let changed = joined != *current;
        (joined, changed)
    }
}

impl<'analyzer, 'src, 'node, 'nodes> cfg::transfer::BlockTransfer
    for ForTransfer<'analyzer, 'src, 'node, 'nodes>
{
    type State = BlockState;
    type Error = ();

    fn transfer_block(
        &mut self,
        _cfg: &cfg::Cfg,
        block: &cfg::BasicBlock,
        state: &Self::State,
    ) -> Result<Vec<cfg::transfer::TransferEdge<Self::State>>, Self::Error> {
        let edge = |target, state| cfg::transfer::TransferEdge { target, state };
        Ok(match block.id {
            cfg::BlockId(0) => vec![edge(cfg::BlockId(1), state.clone())],
            cfg::BlockId(1) => {
                let mut body_environment = state.environment.clone();
                self.analyzer.bind_for_target(
                    self.index,
                    self.element_type.clone(),
                    &mut body_environment,
                );
                vec![
                    edge(
                        cfg::BlockId(3),
                        BlockState::with_values(
                            state.environment.clone(),
                            Vec::new(),
                            Flow::normal(),
                        ),
                    ),
                    edge(
                        cfg::BlockId(2),
                        BlockState::with_values(body_environment, Vec::new(), Flow::normal()),
                    ),
                ]
            }
            cfg::BlockId(2) => {
                let mut body_environment = state.environment.clone();
                let body_result = self.statements.map_or_else(
                    || Eval::value(Type::Nil),
                    |statements| {
                        self.analyzer
                            .eval_statements(statements, &mut body_environment)
                    },
                );
                let body_terminal_flow = body_result
                    .flow
                    .without(FlowKind::Normal)
                    .without(FlowKind::Break)
                    .without(FlowKind::Next);
                self.terminal_flow = self.terminal_flow.union(body_terminal_flow);
                if !body_terminal_flow.is_empty() {
                    self.abrupt = self.abrupt.join(
                        &body_result
                            .abrupt
                            .without(FlowKind::Break)
                            .without(FlowKind::Next),
                    );
                }
                if body_result.flow.contains(FlowKind::Break) {
                    self.break_type = self.break_type.join(&body_result.abrupt.break_type);
                }
                let mut edges = Vec::new();
                if body_result.flow.contains(FlowKind::Break) {
                    edges.push(edge(
                        cfg::BlockId(3),
                        BlockState::with_values(
                            body_environment.clone(),
                            Vec::new(),
                            Flow::normal(),
                        ),
                    ));
                }
                if body_result.flow.contains(FlowKind::Normal)
                    || body_result.flow.contains(FlowKind::Next)
                {
                    edges.push(edge(
                        cfg::BlockId(1),
                        BlockState::with_values(body_environment, Vec::new(), Flow::normal()),
                    ));
                }
                edges
            }
            cfg::BlockId(3) => Vec::new(),
            _ => Vec::new(),
        })
    }

    fn join_state(
        &mut self,
        current: Option<&Self::State>,
        incoming: Self::State,
    ) -> (Self::State, bool) {
        let Some(current) = current else {
            return (incoming, true);
        };
        let joined = current.join(&incoming);
        let changed = joined != *current;
        (joined, changed)
    }
}

impl<'src> Analyzer<'src> {
    /// Run the generic CFG transfer over a complete, straight-line method
    /// body. Bodies with dispatch, branches, or exceptional control flow stay
    /// on the recursive evaluator until their owned transfer exists; the
    /// preflight is important because a failed transfer must not leave partial
    /// diagnostics or recorded types behind.
    pub(super) fn eval_cfg_body<'node>(
        &mut self,
        body_node: &Node<'node>,
        body_id: hir::BodyId,
        environment: &mut Environment,
    ) -> Option<Eval> {
        if !body_can_transfer(&self.hir_program, body_id) {
            return None;
        }
        // The graph is syntax-only and immutable. It is lowered once when the
        // analyzer is created, then reused across seed, fixpoint, and final
        // passes instead of rebuilding the same body for every method visit.
        let graph_store = self.cfg_graphs.as_ref()?.clone();
        let graph = graph_store.get(body_id.0 as usize)?;
        let fixed_array_candidates = graph
            .blocks
            .iter()
            .flat_map(|block| block.operations.iter())
            .filter_map(|operation| {
                let result = operation.result?;
                let cfg::OperationKind::BuildArray { elements } = &operation.kind else {
                    return None;
                };
                let elements = elements
                    .iter()
                    .map(|element| match element {
                        cfg::ArrayOperand::Value(value) => Some(*value),
                        cfg::ArrayOperand::Splat(_) => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some((result, elements))
            })
            .collect::<HashMap<_, _>>();
        let splatted_values = graph
            .blocks
            .iter()
            .flat_map(|block| block.operations.iter())
            .filter_map(|operation| match &operation.kind {
                cfg::OperationKind::Call { arguments, .. } => Some(arguments),
                _ => None,
            })
            .flat_map(|arguments| arguments.iter())
            .filter_map(|argument| match argument {
                cfg::ArgumentOperand::Splat(value) => Some(*value),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let fixed_array_elements = fixed_array_candidates
            .into_iter()
            .filter(|(value, _)| splatted_values.contains(value))
            .collect::<HashMap<_, _>>();
        let mut nodes = SpanNodeIndex::default();
        nodes.visit(body_node);
        if graph.blocks.iter().any(|block| {
            block.unwind.is_some()
                || block.operations.iter().any(|operation| {
                    matches!(
                        operation.kind,
                        cfg::OperationKind::Const { .. }
                            | cfg::OperationKind::Read { .. }
                            | cfg::OperationKind::ReadSpecial { .. }
                            | cfg::OperationKind::Write { .. }
                            | cfg::OperationKind::Call { .. }
                            | cfg::OperationKind::BuildArray { .. }
                            | cfg::OperationKind::BuildHash { .. }
                            | cfg::OperationKind::PatternTest { .. }
                    ) && !nodes
                        .nodes
                        .contains_key(&(operation.span.start as usize, operation.span.end as usize))
                })
                || block.operations.iter().any(|operation| {
                    !matches!(
                        operation.kind,
                        cfg::OperationKind::Const { .. }
                            | cfg::OperationKind::Read { .. }
                            | cfg::OperationKind::ReadSpecial { .. }
                            | cfg::OperationKind::Write { .. }
                            | cfg::OperationKind::Call { .. }
                            | cfg::OperationKind::BuildArray { .. }
                            | cfg::OperationKind::BuildHash { .. }
                            | cfg::OperationKind::PatternTest { .. }
                    )
                })
                || matches!(block.terminator, cfg::Terminator::Raise(_))
        }) {
            return None;
        }

        let body = self.hir_program.body(body_id)?;
        let context = BodyContext {
            body: body_id,
            method: environment.method_key.clone(),
            self_type: environment.self_type.clone(),
            parameters: body.parameters.clone(),
            strictness: self.strictness_at(body.span.start as usize),
        };
        let initial = BlockState::with_values(environment.clone(), Vec::new(), Flow::normal());
        let mut transfer = BodyTransfer {
            analyzer: self,
            context,
            nodes: &nodes,
            fixed_array_elements,
            normal_type: Type::Never,
            abrupt: OutcomeTypes::default(),
            terminal_flow: Flow::empty(),
            final_environment: None,
        };
        let worklist = cfg::transfer::run(&graph, &mut transfer, initial).ok()?;
        let normal_type = transfer.normal_type.clone();
        let abrupt = transfer.abrupt.clone();
        let terminal_flow = transfer.terminal_flow;
        let final_environment = transfer.final_environment.clone()?;
        drop(worklist);
        drop(transfer);
        self.cfg_transfer_bodies = self.cfg_transfer_bodies.saturating_add(1);
        *environment = final_environment;
        let mut result = Eval::from_parts(
            Some(normal_type),
            abrupt,
            Flow::normal().union(terminal_flow),
        );
        result.type_ = self.record(body_node, result.type_.clone());
        Some(result)
    }

    /// Transfer value-producing HIR operations whose semantics do not depend
    /// on a method dispatch. The Prism node is retained only for source
    /// recording and inline assertions; the operation kind and read place
    /// come from owned HIR.
    pub(super) fn eval_cfg_value_dispatch<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let kind = self.hir_value_kind_for_node(node)?;
        match kind {
            ExprKind::Nil
            | ExprKind::Literal(_)
            | ExprKind::Read(_)
            | ExprKind::Array(_)
            | ExprKind::Hash(_) => {
                self.cfg_transfer_values = self.cfg_transfer_values.saturating_add(1);
                Some(self.transfer_cfg_value(node, kind, environment))
            }
            _ => None,
        }
    }

    fn hir_value_kind_for_node(&self, node: &Node<'_>) -> Option<ExprKind> {
        let span = prism::span(node);
        let expression_id = self.hir_value_ids.get(&span)?;
        let expression = self.hir_program.expression(*expression_id)?;
        match &expression.kind {
            ExprKind::Nil
            | ExprKind::Literal(_)
            | ExprKind::Read(_)
            | ExprKind::Array(_)
            | ExprKind::Hash(_) => Some(expression.kind.clone()),
            _ => None,
        }
    }

    fn transfer_cfg_value<'node>(
        &mut self,
        node: &Node<'node>,
        kind: ExprKind,
        environment: &mut Environment,
    ) -> Eval {
        let type_ = match kind {
            ExprKind::Nil => Type::Nil,
            ExprKind::Literal(literal) => Self::cfg_literal_type(&literal),
            ExprKind::Read(read) => self.transfer_cfg_read(node, read, environment),
            ExprKind::Array(elements) => {
                return self.transfer_cfg_array(node, elements, environment);
            }
            ExprKind::Hash(elements) => {
                return self.transfer_cfg_hash(node, elements, environment);
            }
            _ => unreachable!("non-value HIR operation reached CFG value transfer"),
        };
        Eval::value(self.record(node, type_))
    }

    fn transfer_cfg_array<'node>(
        &mut self,
        node: &Node<'node>,
        elements: Vec<ArrayElement>,
        environment: &mut Environment,
    ) -> Eval {
        let Some(array) = node.as_array_node() else {
            return Eval::value(self.record(node, Type::Any));
        };
        let prism_elements = array.elements().into_iter().collect::<Vec<_>>();
        if prism_elements.len() != elements.len() {
            return Eval::value(self.record(node, Type::Any));
        }

        let tuple_depth = self.literal_tuple_depth;
        self.literal_tuple_depth += 1;
        let mut element_types = Vec::new();
        let mut fixed_length = true;
        let mut element = Type::Never;
        for (hir_element, prism_element) in elements.into_iter().zip(prism_elements) {
            let (value_node, splat) = match hir_element {
                ArrayElement::Value(_) => (prism_element, false),
                ArrayElement::Splat(_) => {
                    let value_node = prism_element
                        .as_splat_node()
                        .and_then(|splat| splat.expression())
                        .unwrap_or(prism_element);
                    (value_node, true)
                }
            };
            let child_type = self.eval_node(&value_node, environment).type_;
            let child_type = if splat {
                fixed_length = false;
                self.array_element_type(&child_type)
            } else {
                child_type
            };
            element_types.push(child_type.clone());
            element = element.join(&child_type);
        }
        self.literal_tuple_depth = tuple_depth;
        let element = if element.is_never() {
            if (self.preserve_literal_tuples || self.preserve_nested_literal_tuples)
                && tuple_depth > 0
            {
                Type::Never
            } else {
                Type::Any
            }
        } else {
            element
        };
        let inferred = if fixed_length
            && ((self.preserve_literal_tuples && tuple_depth == 0)
                || (self.preserve_nested_literal_tuples && tuple_depth > 0)
                || self.expected_return_type.as_ref().is_some_and(|expected| {
                    tuple_depth == 0
                        && matches!(expected, Type::Tuple(elements) if elements.len() == element_types.len())
                }))
        {
            Type::Tuple(element_types)
        } else {
            Type::Array(Box::new(element))
        };
        let type_ = self.apply_inline_assertion_in_environment(node, inferred, environment);
        Eval::value(self.record(node, type_))
    }

    fn transfer_cfg_hash<'node>(
        &mut self,
        node: &Node<'node>,
        elements: Vec<HashElement>,
        environment: &mut Environment,
    ) -> Eval {
        let prism_elements = if let Some(hash) = node.as_hash_node() {
            hash.elements().into_iter().collect::<Vec<_>>()
        } else if let Some(hash) = node.as_keyword_hash_node() {
            hash.elements().into_iter().collect::<Vec<_>>()
        } else {
            return Eval::value(self.record(node, Type::Any));
        };
        if prism_elements.len() != elements.len() {
            return Eval::value(self.record(node, Type::Any));
        }

        let mut key = Type::Never;
        let mut value = Type::Never;
        for (hir_element, prism_element) in elements.into_iter().zip(prism_elements) {
            match hir_element {
                HashElement::Pair { .. } => {
                    let Some(assoc) = prism_element.as_assoc_node() else {
                        return Eval::value(self.record(node, Type::Any));
                    };
                    key = key.join(&self.eval_node(&assoc.key(), environment).type_);
                    value = value.join(&self.eval_node(&assoc.value(), environment).type_);
                }
                HashElement::Splat(_) => {
                    let Some(splat) = prism_element.as_assoc_splat_node() else {
                        return Eval::value(self.record(node, Type::Any));
                    };
                    if let Some(expression) = splat.value() {
                        match self.eval_node(&expression, environment).type_ {
                            Type::Hash(splat_key, splat_value) => {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                            }
                            Type::Any => {
                                key = Type::Any;
                                value = Type::Any;
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        let key = if key.is_never() { Type::Any } else { key };
        let value = if value.is_never() { Type::Any } else { value };
        let type_ = self.apply_inline_assertion_in_environment(
            node,
            Type::Hash(Box::new(key), Box::new(value)),
            environment,
        );
        Eval::value(self.record(node, type_))
    }

    fn cfg_literal_type(literal: &Literal) -> Type {
        match literal {
            Literal::Nil => Type::Nil,
            Literal::True => Type::True,
            Literal::False => Type::False,
            Literal::Integer(_) => Type::Integer,
            Literal::Float(_) => Type::Float,
            Literal::Rational(_) => Type::named("Rational"),
            Literal::Imaginary(_) => Type::named("Complex"),
            Literal::String(_) | Literal::XString(_) => Type::String,
            Literal::Symbol(_) => Type::Symbol,
            Literal::RegularExpression(_) => Type::named("Regexp"),
        }
    }

    fn transfer_cfg_read(
        &mut self,
        node: &Node<'_>,
        read: Read,
        environment: &mut Environment,
    ) -> Type {
        match read {
            Read::Local(local) => {
                let name = self
                    .hir_program
                    .local_name(local)
                    .map_or_else(String::new, |name| name.as_str().to_owned());
                self.apply_inline_assertion_in_environment(
                    node,
                    environment.get(&name),
                    environment,
                )
            }
            Read::InstanceVariable(name) => {
                let actual = self.ivar_type(environment, name.as_str());
                self.apply_inline_assertion_in_environment(node, actual, environment)
            }
            Read::ClassVariable(name) => {
                let actual = self.class_var_type(environment, name.as_str());
                self.apply_inline_assertion(node, actual)
            }
            Read::Global(name) => {
                let name = name.as_str().to_owned();
                self.record_shared_read(SharedKey::Global(name.clone()), environment);
                self.apply_inline_assertion(
                    node,
                    self.globals.get(&name).cloned().unwrap_or(Type::Any),
                )
            }
            Read::Constant(path) => {
                let name = path.as_str().to_owned();
                let actual = self.constant_type(environment, &name);
                self.report_missing_constant_if_needed(node, environment, &name);
                self.apply_inline_assertion(node, actual)
            }
            Read::SelfValue => self.apply_inline_assertion(node, environment.self_type.clone()),
            Read::Numbered(number) => {
                self.apply_inline_assertion(node, environment.get(&format!("_{number}")))
            }
            Read::It => self.apply_inline_assertion(node, environment.get("it")),
            Read::BackReference(_) => self.apply_inline_assertion(node, Type::Any),
        }
    }

    pub(super) fn has_cfg_call_operation(&self, node: &Node<'_>) -> bool {
        self.cfg_index
            .as_ref()
            .is_some_and(|index| index.has_call(prism::span(node)))
    }

    pub(super) fn has_cfg_assignment_operation(&self, node: &Node<'_>) -> bool {
        let span = prism::span(node);
        self.cfg_index
            .as_ref()
            .is_some_and(|index| index.has_call(span) || index.has_write(span))
    }

    fn cfg_conditional_for_node(&self, node: &Node<'_>) -> Option<cfg::Conditional> {
        self.cfg_index
            .as_ref()
            .and_then(|index| index.conditional(prism::span(node)))
            .cloned()
    }

    pub(super) fn report_cfg_fallback(&self, node: &Node<'_>, kind: &str) {
        if self.config.debug {
            eprintln!(
                "[typey] CFG fallback for {kind} at {:?}: no owned transfer is available",
                prism::span(node)
            );
        }
    }

    pub(super) fn transfer_cfg_call<'node>(
        &mut self,
        node: &Node<'node>,
        call: HirCallView<'node>,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_calls = self.cfg_transfer_calls.saturating_add(1);
        // The CFG supplies the dispatch name and argument-shape operation.
        // HirCallView retains only Prism child nodes so the existing transfer
        // machinery can evaluate child expressions until the owned value
        // evaluator lands.
        self.eval_call_result(node, &call, environment)
    }

    pub(super) fn transfer_cfg_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: crate::hir::AssignTarget,
        value: crate::hir::ExprId,
        operator: crate::hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_assignments = self.cfg_transfer_assignments.saturating_add(1);
        if let Some(result) =
            self.transfer_cfg_set_assignment(node, target.clone(), value, &operator, environment)
        {
            return result;
        }
        self.eval_hir_assignment(node, target, value, operator, environment)
    }

    /// Transfer direct storage writes from owned HIR. Compound writes and
    /// attribute/index targets still use the established dispatch helpers
    /// until their read/branch/write sequence is driven by block state.
    fn transfer_cfg_set_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: hir::AssignTarget,
        value_id: hir::ExprId,
        operator: &hir::AssignOperator,
        environment: &mut Environment,
    ) -> Option<Eval> {
        if !matches!(operator, hir::AssignOperator::Set) {
            return None;
        }
        let value_node = self.assignment_value_node(node)?;
        debug_assert!(self.hir_program.expression(value_id).is_some());
        match target {
            hir::AssignTarget::Local(local) => {
                let name = self.hir_program.local_name(local)?.as_str().to_owned();
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                if let Some(alias) = self.predicate_alias_for_value(&value_node, environment) {
                    environment.bind_predicate_alias(name.clone(), type_.clone(), alias);
                } else {
                    environment.bind(name.clone(), type_.clone());
                }
                if value_node
                    .as_array_node()
                    .is_some_and(|array| array.elements().is_empty())
                    && matches!(&type_, Type::Array(element) if element.is_any())
                {
                    environment.open_array_locals.insert(name);
                }
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::InstanceVariable(name) => {
                let name = name.as_str().to_owned();
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                let type_ =
                    self.preserve_typed_empty_array_ivar(environment, &name, &value_node, type_);
                let provisional = value_node
                    .as_local_variable_read_node()
                    .is_some_and(|local| {
                        environment.is_provisional(&prism::constant_name(local.name()))
                    });
                self.observe_ivar(environment, name.clone(), &type_, provisional);
                environment.bind(ivar_refinement_key(&name), type_.clone());
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::ClassVariable(name) => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Global(name) => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_global(name.as_str().to_owned(), &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Constant(name) => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let name = name.as_str().to_owned();
                let struct_type = self.struct_subclass_type(environment, &value_node, &name);
                if let Some(struct_type) = struct_type.as_ref() {
                    self.eval_dynamic_struct_block(&value_node, struct_type, environment);
                }
                let type_ = self.apply_inline_assertion(node, struct_type.unwrap_or(actual));
                self.observe_constant(environment, name, &type_);
                Some(Eval::value(self.record(node, type_)))
            }
            hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. } => None,
        }
    }

    pub(super) fn eval_cfg_for<'node>(
        &mut self,
        node: &Node<'node>,
        for_node: &ruby_prism::ForNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_loops = self.cfg_transfer_loops.saturating_add(1);
        let collection = for_node.collection();
        let collection_result = self.eval_node(&collection, environment);
        if !collection_result.flow.contains(FlowKind::Normal) {
            let mut collection_result = collection_result;
            collection_result.type_ = self.record(node, collection_result.type_.clone());
            return collection_result;
        }
        let element_type = self.array_element_type(&collection_result.type_);
        let entry = environment.clone();
        let index = for_node.index();
        let statements = for_node.statements();
        let mut transfer = ForTransfer {
            analyzer: self,
            index: &index,
            statements: statements.as_ref(),
            element_type,
            abrupt: collection_result
                .abrupt
                .without(FlowKind::Break)
                .without(FlowKind::Next),
            break_type: Type::Never,
            terminal_flow: collection_result
                .flow
                .without(FlowKind::Normal)
                .without(FlowKind::Break)
                .without(FlowKind::Next),
        };
        let initial = BlockState::with_values(entry.clone(), Vec::new(), Flow::normal());
        let worklist = cfg::transfer::run(loop_graph(), &mut transfer, initial)
            .expect("the synthetic for CFG is valid");
        let abrupt = transfer.abrupt.clone();
        let break_type = transfer.break_type.clone();
        let terminal_flow = transfer.terminal_flow;
        drop(transfer);
        let head_environment = worklist
            .states
            .get(cfg::BlockId(1).0 as usize)
            .and_then(Option::as_ref)
            .map(|state| state.environment.clone())
            .unwrap_or_else(|| entry.clone());
        let mut result_environment = entry.join(&head_environment);
        if let Some(exit_environment) = worklist
            .states
            .get(cfg::BlockId(3).0 as usize)
            .and_then(Option::as_ref)
            .map(|state| state.environment.clone())
        {
            result_environment = result_environment.join(&exit_environment);
        }
        *environment = result_environment;
        let mut result = Eval::from_parts(
            Some(Type::union([Type::Nil, break_type])),
            abrupt,
            Flow::normal().union(terminal_flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    pub(super) fn eval_cfg_loop<'node>(
        &mut self,
        node: &Node<'node>,
        predicate: &Node<'node>,
        statements: Option<&ruby_prism::StatementsNode<'node>>,
        environment: &mut Environment,
        predicate_truthy: bool,
    ) -> Eval {
        self.cfg_transfer_loops = self.cfg_transfer_loops.saturating_add(1);
        let entry = environment.clone();
        let initial = BlockState::with_values(entry.clone(), Vec::new(), Flow::normal());
        let mut transfer = LoopTransfer {
            analyzer: self,
            predicate,
            statements,
            predicate_truthy,
            abrupt: OutcomeTypes::default(),
            break_type: Type::Never,
            terminal_flow: Flow::empty(),
        };
        let worklist = cfg::transfer::run(loop_graph(), &mut transfer, initial)
            .expect("the synthetic loop CFG is valid");
        let abrupt = transfer.abrupt.clone();
        let break_type = transfer.break_type.clone();
        let terminal_flow = transfer.terminal_flow;
        drop(transfer);
        let head_environment = worklist
            .states
            .get(cfg::BlockId(1).0 as usize)
            .and_then(Option::as_ref)
            .map(|state| state.environment.clone())
            .unwrap_or_else(|| entry.clone());
        let mut result_environment = entry.join(&head_environment);
        if let Some(exit_environment) = worklist
            .states
            .get(cfg::BlockId(3).0 as usize)
            .and_then(Option::as_ref)
            .map(|state| state.environment.clone())
        {
            result_environment = result_environment.join(&exit_environment);
        }
        *environment = result_environment;
        let mut result = Eval::from_parts(
            Some(Type::union([Type::Nil, break_type])),
            abrupt,
            Flow::normal().union(terminal_flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    pub(super) fn eval_if_dispatch<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if self.config.enable_cfg {
            if let Some(conditional) = self.cfg_conditional_for_node(node) {
                return self.transfer_cfg_if(node, if_node, conditional, environment);
            }
            self.cfg_transfer_fallbacks = self.cfg_transfer_fallbacks.saturating_add(1);
            self.report_cfg_fallback(node, "conditional");
        }
        self.eval_if(node, if_node, environment)
    }

    fn transfer_cfg_if<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        conditional: cfg::Conditional,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_conditionals = self.cfg_transfer_conditionals.saturating_add(1);
        let predicate = if_node.predicate();
        let then_node = if_node.statements().map(|statements| statements.as_node());
        let subsequent = if_node.subsequent();
        self.eval_cfg_conditional_paths(
            node,
            &predicate,
            then_node,
            subsequent,
            if_node,
            conditional,
            environment,
        )
    }

    fn eval_cfg_conditional_paths<'node>(
        &mut self,
        node: &Node<'node>,
        predicate: &Node<'node>,
        then_node: Option<Node<'node>>,
        subsequent: Option<Node<'node>>,
        if_node: &IfNode<'node>,
        conditional: cfg::Conditional,
        environment: &mut Environment,
    ) -> Eval {
        debug_assert_ne!(conditional.truthy, conditional.falsy);
        debug_assert_ne!(conditional.join, conditional.truthy);
        debug_assert_ne!(conditional.join, conditional.falsy);

        let previous_defer_inline_assertions = self.defer_inline_assertions;
        self.defer_inline_assertions = true;
        let predicate_type = self
            .eval_node(predicate, environment)
            .normal_type
            .unwrap_or(Type::Never);
        self.defer_inline_assertions = previous_defer_inline_assertions;
        let (then_reachable, else_reachable) =
            self.predicate_reachability(predicate, environment, &predicate_type);
        let report_unreachable = self.should_report_unreachable_branch(node)
            && self.predicate_is_precise(predicate, environment);
        let then_first = if_node
            .statements()
            .and_then(|statements| statements.body().into_iter().next());
        let else_first = subsequent.as_ref().and_then(|subsequent| {
            subsequent
                .as_else_node()
                .and_then(|else_clause| else_clause.statements())
                .and_then(|statements| statements.body().into_iter().next())
        });
        let initial = ConditionalState {
            block: BlockState::with_values(environment.clone(), Vec::new(), Flow::normal()),
            result: Eval::unreachable(),
            path_reachable: true,
        };
        let mut transfer = ConditionalTransfer {
            analyzer: self,
            predicate,
            then_node: then_node.as_ref(),
            subsequent: subsequent.as_ref(),
            then_first: then_first.as_ref(),
            else_first: else_first.as_ref(),
            then_reachable,
            else_reachable,
            report_unreachable,
        };
        let worklist = cfg::transfer::run(conditional_graph(), &mut transfer, initial)
            .expect("the synthetic conditional CFG is valid");
        drop(transfer);
        let joined_state = worklist
            .states
            .get(cfg::BlockId(3).0 as usize)
            .and_then(Option::as_ref)
            .expect("conditional transfer reaches its join block");
        *environment = joined_state.block.environment.clone();
        let mut result = joined_state.result.clone();
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment(name: &str, type_: Type) -> Environment {
        let mut environment = Environment::default();
        environment.bind(name, type_);
        environment
    }

    #[test]
    fn normal_path_wins_over_an_abrupt_path() {
        let normal = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let returned = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::abrupt(FlowKind::Return),
        );

        let joined = normal.join(&returned);

        assert_eq!(joined.environment.get("value"), Type::String);
        assert_eq!(joined.values, vec![Some(Type::String.join(&Type::Integer))]);
        assert!(joined.flow.contains(FlowKind::Normal));
        assert!(joined.flow.contains(FlowKind::Return));
    }

    #[test]
    fn two_normal_paths_join_values_and_environment_facts() {
        let left = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::normal(),
        );

        let joined = left.join(&right);

        let expected = Type::String.join(&Type::Integer);
        assert_eq!(joined.environment.get("value"), expected);
        assert_eq!(joined.values, vec![Some(expected)]);
    }

    #[test]
    fn missing_value_on_one_edge_is_not_invented_at_the_join() {
        let left = BlockState::with_values(
            Environment::default(),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(Environment::default(), vec![None], Flow::normal());

        assert_eq!(left.join(&right).values, vec![None]);
    }
}
