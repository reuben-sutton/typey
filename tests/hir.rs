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
}

#[test]
fn unsupported_syntax_is_explicit_and_source_mapped() {
    let source = "defined?(value)";
    let program = expressions(source);
    assert!(program
        .expressions
        .iter()
        .any(|expression| matches!(expression.kind, ExprKind::Unsupported(_))));
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
}
