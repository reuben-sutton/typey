use typey::hir::{lower, Argument, AssignOperator, AssignTarget, ExprKind, FileId, Receiver};

fn expressions(source: &str) -> typey::hir::Program {
    lower(FileId(7), source.as_bytes())
}

#[test]
fn lowers_calls_with_owned_spans_and_argument_shape() {
    let source = "receiver&.call(1, *values, flag: 2, **options, &block)";
    let program = expressions(source);
    let call = program
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Call(call) if call.name.as_str() == "call" => Some((expression, call)),
            _ => None,
        })
        .expect("call is lowered");

    assert_eq!(call.0.span.file, FileId(7));
    assert_eq!(
        (call.0.span.start, call.0.span.end),
        (0, source.len() as u32)
    );
    assert!(call.1.safe_navigation);
    assert!(matches!(call.1.receiver, Receiver::Explicit(_)));
    assert!(matches!(
        call.1.arguments.as_slice(),
        [
            Argument::Positional(_),
            Argument::Splat(_),
            Argument::Keyword { .. },
            Argument::KeywordSplat(_)
        ]
    ));
    assert_eq!(call.1.argument_groups, vec![1, 2, 4]);
    assert_eq!(call.1.argument_spans.len(), 3);
    assert_eq!(
        call.1
            .argument_spans
            .iter()
            .map(|span| &source[span.start as usize..span.end as usize])
            .collect::<Vec<_>>(),
        vec!["1", "*values", "flag: 2, **options"]
    );
    let keyword_name_span = call
        .1
        .arguments
        .iter()
        .find_map(|argument| match argument {
            Argument::Keyword { name_span, .. } => Some(name_span),
            _ => None,
        })
        .expect("keyword name span");
    assert_eq!(
        &source[keyword_name_span.start as usize..keyword_name_span.end as usize],
        "flag:"
    );
    assert!(matches!(
        call.1.block,
        Some(typey::hir::BlockArgument::Passed(_))
    ));
}

#[test]
fn distinguishes_implicit_super_yield_and_forwarding_calls() {
    let source = r#"def wrapper(...)
  target(...)
  super
  yield(1)
end
"#;
    let program = expressions(source);
    let calls = program
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            ExprKind::Call(call) => Some(call),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(calls.iter().any(|call| {
        call.name.as_str() == "target"
            && matches!(call.receiver, Receiver::Implicit)
            && matches!(call.arguments.as_slice(), [Argument::Forwarded])
    }));
    assert!(calls
        .iter()
        .any(|call| { call.name.as_str() == "super" && matches!(call.receiver, Receiver::Super) }));
    assert!(calls
        .iter()
        .any(|call| { call.name.as_str() == "yield" && matches!(call.receiver, Receiver::Yield) }));
    assert!(program
        .bodies
        .iter()
        .flat_map(|body| body.parameters.parameters.iter())
        .any(|parameter| parameter.kind == typey::hir::ParameterKind::Forwarded));
}

#[test]
fn lowers_inline_blocks_as_owned_closures() {
    let program = expressions("receiver.call(1) { |value| value }");
    let call = program
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Call(call) if call.name.as_str() == "call" => Some(call),
            _ => None,
        })
        .expect("call is lowered");
    let Some(typey::hir::BlockArgument::Inline(closure)) = call.block else {
        panic!("inline block is not represented as a closure");
    };
    let closure = program.closures.get(closure.0 as usize).expect("closure");
    assert_eq!(closure.kind, typey::hir::ClosureKind::Block);
    let body = &program.bodies[closure.body.0 as usize];
    assert!(closure.span.start <= program.expressions[body.root.0 as usize].span.start);
    assert!(closure.span.end >= program.expressions[body.root.0 as usize].span.end);
    assert_eq!(closure.parameters.parameters.len(), 1);
    assert_eq!(
        closure.parameters.parameters[0]
            .name
            .as_ref()
            .map(|name| name.as_str()),
        Some("value")
    );
}

#[test]
fn lowers_else_statement_bodies_as_owned_hir() {
    let program = expressions("if flag\n  left\nelse\n  \"missing\"\nend");
    let if_expression = program
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::If { else_body, .. } => Some(else_body.expect("else body")),
            _ => None,
        })
        .expect("if expression");
    let else_body = program
        .expression(if_expression)
        .expect("else body expression");
    assert!(matches!(else_body.kind, ExprKind::Sequence(_)));
    assert!(!matches!(else_body.kind, ExprKind::Unsupported(_)));
}

#[test]
fn preserves_transparent_loop_predicate_spans() {
    let source = "while (current = value)\nend";
    let program = expressions(source);
    let loop_expression = program
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Loop(loop_expression) => Some(loop_expression),
            _ => None,
        })
        .expect("loop expression");
    let span = loop_expression.condition_span;
    assert_eq!(
        &source[span.start as usize..span.end as usize],
        "(current = value)"
    );
}

#[test]
fn lowers_assignment_targets_and_preserves_operators() {
    let source = r#"local = 1
@ivar = local
@@class_var ||= local
$global &&= local
Constant += local
object.attr = local
values[index] = local
object.attr &&= local
values[index] ||= local
"#;
    let program = expressions(source);
    let assignments = program
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            ExprKind::Assign {
                target,
                target_span,
                operator,
                ..
            } => Some((target, target_span, operator)),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(assignments.len(), 9, "all writes remain assignments");
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Local(_)
    ) && matches!(
        operator,
        AssignOperator::Set
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::InstanceVariable(_)
    ) && matches!(
        operator,
        AssignOperator::Set
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::ClassVariable(_)
    ) && matches!(
        operator,
        AssignOperator::Or
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Global(_)
    ) && matches!(
        operator,
        AssignOperator::And
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Constant(_)
    ) && matches!(
        operator,
        AssignOperator::Binary(_)
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Attribute { .. }
    ) && matches!(
        operator,
        AssignOperator::Set
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Index { .. }
    ) && matches!(
        operator,
        AssignOperator::Set
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Attribute { .. }
    ) && matches!(
        operator,
        AssignOperator::And
    )));
    assert!(assignments.iter().any(|(target, _, operator)| matches!(
        target,
        AssignTarget::Index { .. }
    ) && matches!(
        operator,
        AssignOperator::Or
    )));

    let attribute_span = assignments
        .iter()
        .find_map(|(target, span, operator)| {
            (matches!(target, AssignTarget::Attribute { .. })
                && matches!(operator, AssignOperator::Set))
            .then_some(*span)
        })
        .expect("plain attribute target span");
    assert_eq!(
        &source[attribute_span.start as usize..attribute_span.end as usize],
        "object.attr"
    );
    let local = assignments
        .iter()
        .find_map(|(target, _, _)| match target {
            AssignTarget::Local(local) => Some(*local),
            _ => None,
        })
        .expect("local target");
    assert_eq!(
        program.local_name(local).map(|name| name.as_str()),
        Some("local")
    );
}

#[test]
fn lowers_defined_operands_into_owned_hir() {
    let source = "value = nil\ndefined?(value)";
    let program = expressions(source);
    let operand = program
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Defined { value } => Some(*value),
            _ => None,
        })
        .expect("defined expression");
    assert!(matches!(
        program
            .expression(operand)
            .map(|expression| &expression.kind),
        Some(ExprKind::Read(_))
    ));
}

#[test]
fn lowers_calls_nested_in_default_parameters() {
    let program = expressions(
        r#"def print_changes(path = File.expand_path("."))
  path
end
"#,
    );
    assert!(program.expressions.iter().any(|expression| {
        matches!(&expression.kind, ExprKind::Call(call) if call.name.as_str() == "expand_path")
    }));
    let default_body = program
        .bodies
        .iter()
        .flat_map(|body| body.parameters.parameters.iter())
        .find_map(|parameter| parameter.default_body)
        .expect("default body");
    assert!(matches!(
        program
            .body(default_body)
            .and_then(|body| program.expression(body.root))
            .map(|expression| &expression.kind),
        Some(ExprKind::Call(call)) if call.name.as_str() == "expand_path"
    ));
}

#[test]
fn lowers_assignments_nested_in_unsupported_parents() {
    let program = expressions(
        r#"value = 1
case value
when Integer
  value = 2
end
for item in [value]
  value = item
end
"#,
    );
    let assignments = program
        .expressions
        .iter()
        .filter(|expression| matches!(expression.kind, ExprKind::Assign { .. }))
        .count();
    assert_eq!(assignments, 3);
}

#[test]
fn keeps_executable_children_owned_by_unsupported_parents() {
    let program = expressions(
        r#"for (left, right) in values
  left.to_s
end
"#,
    );
    assert!(program.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            ExprKind::Unsupported(unsupported) if !unsupported.children.is_empty()
        )
    }));
}

#[test]
fn lowers_yield_inside_a_conditional_body() {
    let program = expressions(
        r#"def try
  if block.arity == 0
    yield self
  end
end
"#,
    );
    assert!(
        program.expressions.iter().any(|expression| {
            matches!(&expression.kind, ExprKind::Call(call) if call.name.as_str() == "yield")
        }),
        "{:#?}",
        program.expressions
    );
}

#[test]
fn preserves_positional_hash_arguments_that_prism_labels_as_keyword_hashes() {
    let program = expressions("receiver(\"key\" => 1)");
    let call = program
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Call(call) if call.name.as_str() == "receiver" => Some(call),
            _ => None,
        })
        .expect("receiver call");
    assert!(matches!(
        call.arguments.as_slice(),
        [Argument::Positional(_)]
    ));
}
