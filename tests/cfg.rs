use typey::cfg::{build, ArgumentOperand, OperationKind, Pattern, Terminator};
use typey::hir::{lower, ExprKind, FileId};

fn cfg(source: &str) -> typey::cfg::Cfg {
    let program = lower(FileId(3), source.as_bytes());
    let body = program.root.expect("lowered root body");
    build(&program, body)
}

fn operations(graph: &typey::cfg::Cfg) -> Vec<&typey::cfg::Operation> {
    graph
        .blocks
        .iter()
        .flat_map(|block| block.operations.iter())
        .collect()
}

#[test]
fn lowers_calls_left_to_right_without_flattening_argument_shapes() {
    let graph = cfg("receiver.first(1, *values, flag: 2, **options, &block)");
    let call = operations(&graph)
        .iter()
        .find_map(|operation| match &operation.kind {
            OperationKind::Call {
                name,
                arguments,
                block,
                receiver,
                ..
            } if name.as_str() == "first" => Some((receiver, arguments, block)),
            _ => None,
        })
        .expect("first call operation");
    assert!(matches!(call.0, typey::cfg::ReceiverOperand::Value(_)));
    assert!(matches!(
        call.1.as_slice(),
        [
            ArgumentOperand::Positional(_),
            ArgumentOperand::Splat(_),
            ArgumentOperand::Keyword { .. },
            ArgumentOperand::KeywordSplat(_)
        ]
    ));
    assert!(matches!(call.2, Some(typey::cfg::BlockOperand::Passed(_))));

    let entry = graph.block(graph.entry).expect("entry block");
    let call_index = entry
        .operations
        .iter()
        .position(|operation| {
            matches!(&operation.kind, OperationKind::Call { name, .. } if name.as_str() == "first")
        })
        .expect("call in entry block");
    assert!(entry.operations[..call_index]
        .iter()
        .any(|operation| matches!(operation.kind, OperationKind::Const { .. })));
}

#[test]
fn lowers_safe_navigation_to_nil_and_call_paths() {
    let graph = cfg("receiver&.call(argument)");
    assert!(operations(&graph).iter().any(|operation| matches!(
        operation.kind,
        OperationKind::PatternTest {
            pattern: Pattern::Nil,
            ..
        }
    )));
    assert!(graph
        .blocks
        .iter()
        .any(|block| { matches!(block.terminator, Terminator::Branch { .. }) }));
    assert!(graph.blocks.iter().any(|block| block.parameters.len() == 1));
}

#[test]
fn lowers_if_with_normal_join_and_value_parameter() {
    let graph = cfg("if condition\n  left\nelse\n  right\nend");
    let branch = graph
        .blocks
        .iter()
        .find_map(|block| match block.terminator {
            Terminator::Branch { truthy, falsy, .. } => Some((truthy, falsy)),
            _ => None,
        })
        .expect("conditional branch");
    assert_ne!(branch.0, branch.1);
    assert!(graph.blocks.iter().any(|block| {
        block.parameters.len() == 1 && matches!(block.terminator, Terminator::Return(Some(_)))
    }));
    assert!(
        graph
            .blocks
            .iter()
            .filter(|block| {
                matches!(
                    &block.terminator,
                    Terminator::Jump { arguments, .. } if arguments.len() == 1
                )
            })
            .count()
            >= 2
    );
}

#[test]
fn lowers_compound_assignment_to_read_branch_write_and_join() {
    let graph = cfg("value ||= fallback");
    assert!(operations(&graph).iter().any(|operation| matches!(
        operation.kind,
        OperationKind::PatternTest {
            pattern: Pattern::Truthy,
            ..
        }
    )));
    assert!(operations(&graph)
        .iter()
        .any(|operation| matches!(operation.kind, OperationKind::Write { .. })));
    assert!(graph.blocks.iter().any(|block| {
        block.parameters.len() == 1
            && block
                .parameters
                .first()
                .is_some_and(|parameter| !parameter.incoming.is_empty())
    }));
}

#[test]
fn lowers_loops_with_header_back_edge_break_target_and_next_target() {
    let graph = cfg("while condition\n  next\nend");
    assert!(graph
        .blocks
        .iter()
        .any(|block| { matches!(block.terminator, Terminator::Branch { .. }) }));
    let back_edges = graph
        .blocks
        .iter()
        .filter(|block| {
            matches!(
                block.terminator,
                Terminator::Jump { target, .. } if target == graph.entry || target.0 > block.id.0
            )
        })
        .count();
    assert!(back_edges >= 1, "expected a loop jump: {graph:#?}");
    assert!(graph.blocks.iter().any(|block| {
        block.parameters.len() == 1 && matches!(block.terminator, Terminator::Return(Some(_)))
    }));
}

#[test]
fn lowers_rescue_and_ensure_with_unwind_and_handler_blocks() {
    let graph = cfg(
        "begin\n  risky\nrescue StandardError => error\n  recover(error)\nensure\n  cleanup\nend",
    );
    assert!(graph.blocks.iter().any(|block| block.unwind.is_some()));
    assert!(graph
        .blocks
        .iter()
        .any(|block| !block.parameters.is_empty() && block.unwind.is_none()));
    assert!(operations(&graph).iter().any(|operation| matches!(
        operation.kind,
        OperationKind::PatternTest {
            pattern: Pattern::Case { .. },
            ..
        }
    )));
    assert!(graph
        .blocks
        .iter()
        .any(|block| { matches!(block.terminator, Terminator::Raise(_)) }));
}

#[test]
fn every_lowered_hir_expression_has_a_cfg_value_or_is_abrupt() {
    let source = "value = [1, 2]\nif value\n  value.first\nend";
    let program = lower(FileId(3), source.as_bytes());
    let body = program.root.expect("lowered root body");
    let graph = build(&program, body);
    assert!(program
        .expressions
        .iter()
        .enumerate()
        .all(|(index, expression)| {
            matches!(
                expression.kind,
                ExprKind::Return(_) | ExprKind::Break(_) | ExprKind::Next(_)
            ) || graph.expression_values[index].is_some()
        }));
}
