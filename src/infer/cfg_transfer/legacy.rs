//! Parser-backed CFG adapters retained during the HIR migration.
//!
//! The transfer implementations in the parent module operate on owned CFG
//! state. These entry points still receive Prism nodes because the legacy
//! evaluator has not yet been moved to owned HIR for these specialized control
//! forms. Keeping the adapter here makes that boundary explicit.

use super::*;
use ruby_prism::IfNode;
use std::sync::OnceLock;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ConditionalState {
    pub(super) block: BlockState,
    pub(super) result: Eval,
    pub(super) path_reachable: bool,
}

pub(super) struct ConditionalTransfer<'analyzer, 'src, 'node, 'nodes> {
    pub(super) analyzer: &'analyzer mut Analyzer<'src>,
    pub(super) predicate: &'nodes Node<'node>,
    pub(super) then_node: Option<&'nodes Node<'node>>,
    pub(super) subsequent: Option<&'nodes Node<'node>>,
    pub(super) then_first: Option<&'nodes Node<'node>>,
    pub(super) else_first: Option<&'nodes Node<'node>>,
    pub(super) then_reachable: bool,
    pub(super) else_reachable: bool,
    pub(super) report_unreachable: bool,
}

pub(super) struct LoopTransfer<'analyzer, 'src, 'node, 'nodes> {
    pub(super) analyzer: &'analyzer mut Analyzer<'src>,
    pub(super) predicate: &'nodes Node<'node>,
    pub(super) statements: Option<&'nodes ruby_prism::StatementsNode<'node>>,
    pub(super) predicate_truthy: bool,
    pub(super) abrupt: OutcomeTypes,
    pub(super) break_type: Type,
    pub(super) terminal_flow: Flow,
}

pub(super) struct ForTransfer<'analyzer, 'src, 'node, 'nodes> {
    pub(super) analyzer: &'analyzer mut Analyzer<'src>,
    pub(super) index: &'nodes Node<'node>,
    pub(super) statements: Option<&'nodes ruby_prism::StatementsNode<'node>>,
    pub(super) element_type: Type,
    pub(super) abrupt: OutcomeTypes,
    pub(super) break_type: Type,
    pub(super) terminal_flow: Flow,
}

pub(super) fn conditional_graph() -> &'static cfg::Cfg {
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
        ensure_entries: Vec::new(),
        unsupported_spans: Vec::new(),
        expression_values: Vec::new(),
    })
}

pub(super) fn loop_graph() -> &'static cfg::Cfg {
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
        ensure_entries: Vec::new(),
        unsupported_spans: Vec::new(),
        expression_values: Vec::new(),
    })
}

impl<'src> Analyzer<'src> {
    fn cfg_conditional_for_node(&self, node: &Node<'_>) -> Option<cfg::Conditional> {
        self.cfg_index
            .as_ref()
            .and_then(|index| index.conditional(prism::span(node)))
            .cloned()
    }

    pub(in crate::infer) fn eval_cfg_for<'node>(
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

    pub(in crate::infer) fn eval_cfg_loop<'node>(
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

    pub(in crate::infer) fn eval_if_dispatch<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if self.config.enable_cfg {
            if let Some(conditional) = self.cfg_conditional_for_node(node) {
                return self.transfer_cfg_if(node, if_node, conditional, environment);
            }
            self.record_cfg_fallback(node, "conditional", CfgFallbackKind::UnsupportedOperation);
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
