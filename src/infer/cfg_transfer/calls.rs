//! Shared call-specific semantics for owned CFG transfer.

use super::super::hash_shape::{HashKey, HashShape};
use super::super::{Analyzer, Environment, Eval, OwnedCallInput, UntypedOrigin};
use crate::cfg;
use crate::hir;
use crate::types::Type;
use std::collections::HashMap;
fn compound_assignment_receiver(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: Type,
) -> Type {
    let Some(expression) = input
        .expression
        .and_then(|id| analyzer.program.hir_program.expression(id))
    else {
        return receiver;
    };
    let hir::ExprKind::Assign {
        operator: hir::AssignOperator::Binary(operator),
        ..
    } = &expression.kind
    else {
        return receiver;
    };
    if operator.as_str() == input.name.as_str() {
        // An operator write only reaches the operator call after its
        // getter has produced a normal value. Match Ruby's compound
        // assignment semantics without weakening ordinary `nil + x`
        // dispatch: the getter remains nilable, while the normal path
        // entering `+` is known to be non-nil.
        receiver.without(&Type::Nil)
    } else {
        receiver
    }
}

pub(super) fn transfer_call(
    analyzer: &mut Analyzer<'_>,
    input: OwnedCallInput,
    values: &[Option<Type>],
    fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    hash_shapes: &mut [Option<HashShape>],
    environment: &mut Environment,
) -> Result<Eval, String> {
    analyzer.cfg_transfer_calls = analyzer.cfg_transfer_calls.saturating_add(1);
    let call = input
        .expression
        .and_then(|expression| analyzer.program.hir_program.expression(expression))
        .and_then(|expression| match &expression.kind {
            hir::ExprKind::Call(call) => Some(call.clone()),
            _ => None,
        });
    let call_arguments = if let Some(call) = call {
        let arguments = analyzer
            .cfg_owned_hir_call_arguments(&input, &call, values, fixed_array_elements, environment)
            .ok_or_else(|| "owned HIR call-argument shape is unavailable".to_owned())?;
        arguments.into_call_arguments()
    } else {
        analyzer
            .cfg_owned_call_arguments(&input, values, fixed_array_elements)
            .ok_or_else(|| "owned CFG call-argument shape is unavailable".to_owned())?
    };
    let receiver_type = match &input.receiver {
        cfg::ReceiverOperand::Implicit => environment.self_type.clone(),
        cfg::ReceiverOperand::Value(value) => values
            .get(value.0 as usize)
            .cloned()
            .flatten()
            .ok_or_else(|| "owned receiver value is unavailable".to_owned())?,
        cfg::ReceiverOperand::Super | cfg::ReceiverOperand::Yield => environment.self_type.clone(),
    };
    let receiver_type = compound_assignment_receiver(analyzer, &input, receiver_type);
    let receiver_value = match input.receiver {
        cfg::ReceiverOperand::Value(value) => Some(value),
        _ => None,
    };
    let receiver_hash_shape =
        receiver_value.and_then(|value| hash_shapes.get(value.0 as usize).cloned().flatten());
    let mut block_result = None;
    let dynamic_instance_variable_type = if matches!(
        input.name.as_str(),
        "instance_variable_get" | "instance_variable_set" | "instance_variable_defined?"
    ) {
        analyzer
            .cfg_dynamic_instance_variable_name(&input)
            .and_then(|name| {
                analyzer.eval_dynamic_instance_variable_call_owned(
                    input.name.as_str(),
                    &receiver_type,
                    matches!(input.receiver, cfg::ReceiverOperand::Implicit),
                    Some(&name),
                    &call_arguments.argument_types,
                    environment,
                )
            })
    } else {
        None
    };
    let (type_, untyped_origin) = if let Some(result) = super::intrinsics::transfer_intrinsic_call(
        analyzer,
        &input,
        &receiver_type,
        &call_arguments,
        environment,
    ) {
        result
    } else if let Some(type_) = dynamic_instance_variable_type {
        (type_, UntypedOrigin::Propagated)
    } else if input.name.as_str() == "!" {
        // Unary negation is Ruby's boolean protocol, not a normal method
        // lookup. In particular, it must work for nilable block locals
        // before flow narrowing has selected their non-nil branch.
        (Type::bool(), UntypedOrigin::Propagated)
    } else if matches!(input.receiver, cfg::ReceiverOperand::Yield) {
        let type_ = analyzer
            .cfg_yield_result(input.site, &call_arguments, environment)
            .ok_or_else(|| "yield has no owned block contract".to_owned())?;
        (type_, UntypedOrigin::Propagated)
    } else if matches!(input.receiver, cfg::ReceiverOperand::Super) {
        let context = super::context::transfer_super_call(
            analyzer,
            &input,
            &receiver_type,
            &call_arguments,
            values,
            environment,
        )?;
        block_result = context.block_result;
        (context.type_, context.untyped_origin)
    } else if matches!(input.receiver, cfg::ReceiverOperand::Implicit) {
        let context = super::context::transfer_implicit_call(
            analyzer,
            &input,
            &receiver_type,
            &call_arguments,
            values,
            environment,
        )?;
        block_result = context.block_result;
        (context.type_, context.untyped_origin)
    } else {
        let dispatch_receiver = if input.safe_navigation {
            receiver_type.without(&Type::Nil)
        } else {
            receiver_type.clone()
        };
        if input.safe_navigation
            && !receiver_type.is_any()
            && !receiver_type.is_never()
            && receiver_type.without(&Type::Nil) == receiver_type
        {
            analyzer.error_at(
                input.site,
                format!("Used `&.` operator on `{receiver_type}`, which can never be nil"),
            );
        }
        let receiver = super::dispatch::transfer_receiver_call(
            analyzer,
            &input,
            &dispatch_receiver,
            &call_arguments,
            values,
            environment,
            receiver_hash_shape.as_ref(),
        )?;
        block_result = receiver.block_result;
        (receiver.type_, receiver.untyped_origin)
    };
    update_hash_shape_after_call(
        analyzer,
        &input,
        receiver_value,
        &call_arguments,
        hash_shapes,
        environment,
    );
    let result = super::outcomes::finish_call(
        analyzer,
        &input,
        &receiver_type,
        type_,
        block_result,
        untyped_origin,
        environment,
    );
    Ok(result)
}

fn update_hash_shape_after_call(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    receiver_value: Option<cfg::ValueId>,
    arguments: &super::super::CallArguments<'_>,
    hash_shapes: &mut [Option<HashShape>],
    environment: &mut Environment,
) {
    if input.name.as_str() != "[]=" {
        return;
    }
    let Some(receiver_value) = receiver_value else {
        return;
    };
    let key = assigned_hash_key(analyzer, input)
        .or_else(|| super::builtins::owned_hash_key(analyzer, input));
    let value = arguments.argument_types.last().cloned();
    if let (Some(key), Some(value)) = (key, value) {
        if let Some(shape) = hash_shapes
            .get_mut(receiver_value.0 as usize)
            .and_then(Option::as_mut)
        {
            shape.write(key.clone(), value.clone());
        }
        if let Some(read) = input
            .expression
            .and_then(|id| analyzer.program.hir_program.expression(id))
            .and_then(|expression| match &expression.kind {
                hir::ExprKind::Call(call) => match call.receiver {
                    hir::Receiver::Explicit(receiver) => analyzer
                        .program
                        .hir_program
                        .expression(receiver)
                        .and_then(|receiver| match &receiver.kind {
                            hir::ExprKind::Read(read) => Some(read),
                            _ => None,
                        }),
                    _ => None,
                },
                hir::ExprKind::Assign { target, .. } => match target {
                    hir::AssignTarget::Index { receiver, .. } => analyzer
                        .program
                        .hir_program
                        .expression(*receiver)
                        .and_then(|receiver| match &receiver.kind {
                            hir::ExprKind::Read(read) => Some(read),
                            _ => None,
                        }),
                    _ => None,
                },
                _ => None,
            })
        {
            if let Some(storage_key) = super::assignment::hash_shape_key_for_read(analyzer, read) {
                if let Some(shape) = environment.hash_shape(&storage_key).cloned() {
                    let mut shape = shape;
                    shape.write(key, value);
                    environment.set_hash_shape(storage_key, Some(shape));
                }
            }
        }
    } else if let Some(shape) = hash_shapes.get_mut(receiver_value.0 as usize) {
        *shape = None;
    }
}

fn assigned_hash_key(analyzer: &Analyzer<'_>, input: &OwnedCallInput) -> Option<HashKey> {
    let expression = input
        .expression
        .and_then(|id| analyzer.program.hir_program.expression(id))?;
    let hir::ExprKind::Assign { target, .. } = &expression.kind else {
        return None;
    };
    let hir::AssignTarget::Index { arguments, .. } = target else {
        return None;
    };
    let hir::Argument::Positional(argument) = arguments.first()? else {
        return None;
    };
    super::super::hash_shape::literal_key(&analyzer.program.hir_program, *argument)
}
