use typey::cfg::{build, ArgumentOperand, CfgIndex, OperationKind, Pattern, Terminator};
use typey::hir::{lower, ExprKind, FileId};

fn cfg(source: &str) -> typey::cfg::Cfg {
    let program = lower(FileId(3), source.as_bytes());
    let body = program.root.expect("lowered root body");
    build(&program, body)
}

fn all_cfgs(source: &str) -> Vec<typey::cfg::Cfg> {
    let program = lower(FileId(3), source.as_bytes());
    (0..program.bodies.len())
        .map(|index| build(&program, typey::hir::BodyId(index as u32)))
        .collect()
}

fn operations(graph: &typey::cfg::Cfg) -> Vec<&typey::cfg::Operation> {
    graph
        .blocks
        .iter()
        .flat_map(|block| block.operations.iter())
        .collect()
}

#[test]
fn reserves_distinct_ids_for_nested_inline_closures() {
    let source = r#"
def build(values)
  values.to_h { |value| [value, [value].map { |nested| nested }] }
end
"#;
    let program = lower(FileId(3), source.as_bytes());
    let mut to_h_closure = None;
    let mut map_closure = None;
    for expression in &program.expressions {
        let ExprKind::Call(call) = &expression.kind else {
            continue;
        };
        let Some(typey::hir::BlockArgument::Inline(closure)) = call.block.as_ref() else {
            continue;
        };
        match call.name.as_str() {
            "to_h" => to_h_closure = Some(*closure),
            "map" => map_closure = Some(*closure),
            _ => {}
        }
    }
    assert_ne!(to_h_closure, map_closure);
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
    assert!(operations(&graph).iter().any(|operation| {
        matches!(&operation.kind, OperationKind::Call { name, .. } if name.as_str() == "first")
            && operation.expression.is_some()
    }));
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
fn preserves_special_call_receivers_and_forwarding_in_method_cfgs() {
    let graphs = all_cfgs(
        r#"def wrapper(...)
  target(...)
  super
  yield(1)
end
"#,
    );
    let operations = graphs
        .iter()
        .flat_map(|graph| graph.blocks.iter())
        .flat_map(|block| block.operations.iter())
        .filter_map(|operation| match &operation.kind {
            OperationKind::Call {
                receiver,
                name,
                arguments,
                ..
            } => Some((receiver, name.as_str(), arguments)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(operations.iter().any(|(receiver, name, arguments)| {
        matches!(receiver, typey::cfg::ReceiverOperand::Implicit)
            && *name == "target"
            && matches!(arguments.as_slice(), [ArgumentOperand::Forwarded])
    }));
    assert!(operations.iter().any(|(receiver, name, _)| {
        matches!(receiver, typey::cfg::ReceiverOperand::Super) && *name == "super"
    }));
    assert!(operations.iter().any(|(receiver, name, _)| {
        matches!(receiver, typey::cfg::ReceiverOperand::Yield) && *name == "yield"
    }));
}

#[test]
fn lowers_inline_blocks_as_call_operands_without_executing_the_body() {
    let graph = cfg("receiver.call(1) { |value| value }");
    let has_inline_block = operations(&graph)
        .iter()
        .any(|operation| match &operation.kind {
            OperationKind::Call {
                name,
                block: Some(typey::cfg::BlockOperand::Inline(_)),
                ..
            } if name.as_str() == "call" => true,
            _ => false,
        });
    assert!(has_inline_block, "inline block call");
    assert!(!graph.blocks.iter().any(|block| {
        block
            .operations
            .iter()
            .any(|operation| matches!(operation.kind, OperationKind::ReadSpecial { .. }))
    }));
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
fn records_conditional_hir_identity_and_cfg_targets() {
    let program = lower(FileId(3), b"if condition\n  left\nelse\n  right\nend");
    let body = program.root.expect("lowered root body");
    let graph = build(&program, body);
    let conditional = graph.conditionals.first().expect("conditional region");
    let expression = program
        .expression(conditional.expression)
        .expect("conditional expression");
    assert!(matches!(expression.kind, ExprKind::If { .. }));
    assert!(matches!(
        graph
            .block(conditional.truthy)
            .expect("truthy block")
            .terminator,
        Terminator::Jump { .. } | Terminator::Return(_) | Terminator::Unreachable
    ));
    assert!(matches!(
        graph
            .block(conditional.falsy)
            .expect("falsy block")
            .terminator,
        Terminator::Jump { .. } | Terminator::Return(_) | Terminator::Unreachable
    ));
    assert!(graph
        .block(conditional.join)
        .expect("join block")
        .parameters
        .iter()
        .any(|parameter| !parameter.incoming.is_empty()));
}

#[test]
fn lowers_compound_assignment_to_read_branch_write_and_join() {
    let graph = cfg("value ||= fallback");
    assert!(operations(&graph).iter().any(|operation| matches!(
        operation.kind,
        OperationKind::PatternTest {
            pattern: Pattern::LogicalAnd | Pattern::LogicalOr,
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
fn lowers_attribute_and_index_assignments_to_writer_calls() {
    let graph = cfg("object.value = item\nvalues[index] = item");
    let names = operations(&graph)
        .iter()
        .filter_map(|operation| match &operation.kind {
            OperationKind::Call { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(names.contains(&"value="));
    assert!(names.contains(&"[]="));
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
fn preserves_owned_call_identity_inside_rescue_sequences() {
    let source = "begin\n  raise \"boom\"\nrescue StandardError\n  \"recovered\"\nend";
    let program = lower(FileId(3), source.as_bytes());
    let body = program.root.expect("lowered root body");
    let graph = build(&program, body);
    let raise = operations(&graph)
        .into_iter()
        .find(|operation| {
            matches!(
                &operation.kind,
                OperationKind::Call { name, .. } if name.as_str() == "raise"
            )
        })
        .expect("raise call operation");
    let expression = raise.expression.expect("owned call expression");
    assert!(matches!(
        program.expression(expression).expect("HIR expression").kind,
        ExprKind::Call(_)
    ));
}

#[test]
fn lowers_ensure_completion_after_normal_and_unwind_paths() {
    let graph = cfg(
        "begin\n  raise \"boom\"\nrescue StandardError\n  \"recovered\"\nensure\n  \"cleanup\"\nend",
    );
    assert_eq!(graph.ensure_entries.len(), 1);
    assert!(graph
        .blocks
        .iter()
        .any(|block| { matches!(block.terminator, Terminator::EnsureComplete { .. }) }));
    let ensure_entry = graph.ensure_entries[0];
    assert!(graph
        .blocks
        .iter()
        .any(|block| block.unwind == Some(ensure_entry)));
}

#[test]
fn lowers_retry_to_the_protected_body_entry() {
    let graph = cfg("begin\n  risky\nrescue StandardError\n  retry\nend");
    let retry_target = graph
        .blocks
        .iter()
        .find_map(|block| match block.terminator {
            Terminator::Jump { target, .. }
                if graph
                    .block(target)
                    .is_some_and(|target| target.unwind.is_some()) =>
            {
                Some(target)
            }
            _ => None,
        })
        .expect("retry jump to protected body");
    assert!(graph
        .blocks
        .iter()
        .any(|block| block.unwind == graph.block(retry_target).and_then(|block| block.unwind)));
}

#[test]
fn lowers_rescue_reference_retry_and_ensure_edges() {
    let graph = cfg(
        "begin\n  risky\nrescue StandardError => error\n  retry\nensure\n  cleanup(error)\nend",
    );
    assert!(operations(&graph)
        .iter()
        .any(|operation| matches!(operation.kind, OperationKind::Write { .. })));
    assert!(graph.blocks.iter().any(|block| {
        matches!(&block.terminator, Terminator::Jump { target, arguments } if !arguments.is_empty() && graph.block(*target).is_some_and(|target| !target.parameters.is_empty()))
    }));
    assert!(
        graph
            .blocks
            .iter()
            .filter(|block| block.unwind.is_none())
            .count()
            >= 2
    );
}

#[test]
fn closes_returning_blocks_without_lowering_following_sequence_into_them() {
    let graph = cfg("if flag\n  return value\nend\ntail");
    let return_block = graph
        .blocks
        .iter()
        .find(|block| matches!(block.terminator, Terminator::Return(Some(_))))
        .expect("return block");
    assert!(return_block
        .operations
        .iter()
        .any(|operation| { matches!(operation.kind, OperationKind::Call { .. }) }));
    assert!(!matches!(return_block.terminator, Terminator::Unreachable));
}

#[test]
fn records_unsupported_handoffs_without_hiding_nested_operations() {
    let graph = cfg("for (left, right) in values\n  left.to_s\nend");
    assert!(!graph.unsupported_spans.is_empty());
    assert!(operations(&graph).iter().any(|operation| {
        matches!(&operation.kind, OperationKind::Call { name, .. } if name.as_str() == "to_s")
    }));
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

#[test]
fn streaming_cfg_index_matches_materialized_graphs() {
    let source = "value = 1\nif value\n  value.to_s\nelse\n  value.inspect\nend\n";
    let program = lower(FileId(3), source.as_bytes());
    let graphs = all_cfgs(source);
    let streaming = CfgIndex::from_program(&program);
    let materialized = CfgIndex::from_graphs(&program, &graphs);
    assert_eq!(streaming.body_count(), materialized.body_count());
    assert_eq!(
        streaming.unsupported_count(),
        materialized.unsupported_count()
    );
    for graph in &graphs {
        for block in &graph.blocks {
            for operation in &block.operations {
                let span = (operation.span.start as usize, operation.span.end as usize);
                match operation.kind {
                    OperationKind::Call { .. } => assert!(streaming.has_call(span)),
                    OperationKind::Write { .. } => assert!(streaming.has_write(span)),
                    _ => {}
                }
            }
        }
        for conditional in &graph.conditionals {
            let expression = program
                .expression(conditional.expression)
                .expect("conditional expression");
            let span = (expression.span.start as usize, expression.span.end as usize);
            assert!(streaming.conditional(span).is_some());
        }
    }
}
