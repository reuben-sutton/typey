//! Shared call-specific semantics for owned CFG transfer.

use super::super::{
    proc_parts, Analyzer, Environment, Eval, Flow, FlowKind, OutcomeTypes, OwnedCallInput,
    SourceSite, UntypedOrigin,
};
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
    let has_block = input.block.is_some();
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
        let current_method = environment
            .method_key
            .as_ref()
            .ok_or_else(|| "super call has no enclosing method".to_owned())?;
        let key = analyzer
            .super_method_key(current_method)
            .ok_or_else(|| "super call has no resolvable parent method".to_owned())?;
        analyzer.record_method_dependency(&key, environment);
        if let Some(signature) = analyzer
            .observe_call(&key, &call_arguments, has_block)
            .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
        {
            let callback_result = analyzer.cfg_block_return_type(
                &input,
                &key,
                &signature,
                &call_arguments,
                &receiver_type,
                values,
                environment,
            );
            let block_return_type = callback_result.as_ref().map(Analyzer::block_value_type);
            let type_ = analyzer.invoke_signature_at(
                input.site,
                input.name.as_str(),
                &signature,
                &call_arguments,
                Some(&receiver_type),
                block_return_type.as_ref(),
            );
            block_result = callback_result;
            let origin = analyzer
                .resolve_method_key(&key)
                .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                .is_some_and(|state| state.explicit)
                .then_some(UntypedOrigin::DeclaredSignature)
                .unwrap_or(UntypedOrigin::InferredMethod);
            (type_, origin)
        } else {
            (Type::Any, UntypedOrigin::FallbackCall)
        }
    } else if matches!(input.receiver, cfg::ReceiverOperand::Implicit) {
        if let Some(type_) =
            analyzer.global_call_type(input.name.as_str(), &call_arguments.argument_types)
        {
            (type_, UntypedOrigin::Propagated)
        } else {
            let key = analyzer.implicit_method_key(input.name.as_str(), environment);
            analyzer.record_method_dependency(&key, environment);
            if let Some(signature) = analyzer
                .observe_call(&key, &call_arguments, has_block)
                .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
            {
                let callback_result = analyzer.cfg_block_return_type(
                    &input,
                    &key,
                    &signature,
                    &call_arguments,
                    &receiver_type,
                    values,
                    environment,
                );
                let block_return_type = callback_result.as_ref().map(Analyzer::block_value_type);
                let type_ = analyzer.invoke_signature_at(
                    input.site,
                    input.name.as_str(),
                    &signature,
                    &call_arguments,
                    Some(&receiver_type),
                    block_return_type.as_ref(),
                );
                block_result = callback_result;
                let origin = analyzer
                    .resolve_method_key(&key)
                    .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                    .is_some_and(|state| state.explicit)
                    .then_some(UntypedOrigin::DeclaredSignature)
                    .unwrap_or(UntypedOrigin::InferredMethod);
                (type_, origin)
            } else if let Some(type_) =
                analyzer.cfg_passed_dynamic_method_type(&input, &receiver_type, environment)
            {
                (type_, UntypedOrigin::Propagated)
            } else {
                return Err(format!(
                    "implicit call `{}` has no method or owned dynamic-method contract",
                    input.name.as_str()
                ));
            }
        }
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
        let callable_type = if matches!(input.name.as_str(), "call" | "[]") {
            super::calls::transfer_callable_call(
                analyzer,
                input.site,
                &dispatch_receiver,
                &call_arguments,
            )
        } else {
            None
        };
        if let Some(type_) = callable_type {
            (type_, UntypedOrigin::Propagated)
        } else if input.safe_navigation && dispatch_receiver.is_never() {
            (Type::Nil, UntypedOrigin::FallbackCall)
        } else {
            // `[]` is also ordinary Ruby method dispatch. Only proc-like
            // receivers use the callable shorthand; a nominal receiver
            // must still resolve its declared `[]` method here.
            let key = analyzer.receiver_method_key(
                None,
                &dispatch_receiver,
                input.name.as_str(),
                environment,
            );
            if let Some(key) = key {
                analyzer.record_method_dependency(&key, environment);
                if let Some(signature) = analyzer
                    .observe_call(&key, &call_arguments, has_block)
                    .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
                {
                    let callback_result = analyzer.cfg_block_return_type(
                        &input,
                        &key,
                        &signature,
                        &call_arguments,
                        &dispatch_receiver,
                        values,
                        environment,
                    );
                    let block_return_type =
                        callback_result.as_ref().map(Analyzer::block_value_type);
                    let type_ = analyzer.invoke_signature_at(
                        input.site,
                        input.name.as_str(),
                        &signature,
                        &call_arguments,
                        Some(&dispatch_receiver),
                        block_return_type.as_ref(),
                    );
                    block_result = callback_result;
                    let type_ = if input.name.as_str() == "new" {
                        let type_ = analyzer.instantiate_generic_class(type_);
                        analyzer.default_class_constructor_type(&dispatch_receiver, type_)
                    } else {
                        type_
                    };
                    let origin = analyzer
                        .resolve_method_key(&key)
                        .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                        .is_some_and(|state| state.explicit)
                        .then_some(UntypedOrigin::DeclaredSignature)
                        .unwrap_or(UntypedOrigin::InferredMethod);
                    (type_, origin)
                } else if let Some((type_, callback)) = super::collections::transfer_collection_call(
                    analyzer,
                    &input,
                    &dispatch_receiver,
                    values,
                    environment,
                ) {
                    block_result = callback;
                    (type_, UntypedOrigin::FallbackCall)
                } else if let Some((type_, callback)) = super::builtins::transfer_builtin_call(
                    analyzer,
                    &input,
                    &dispatch_receiver,
                    &call_arguments,
                    values,
                    environment,
                ) {
                    block_result = callback;
                    (type_, UntypedOrigin::FallbackCall)
                } else {
                    return Err(format!(
                        "receiver call `{}` on `{dispatch_receiver}` has no method, collection, or builtin contract",
                        input.name.as_str()
                    ));
                }
            } else if let Some((type_, callback)) = super::collections::transfer_collection_call(
                analyzer,
                &input,
                &dispatch_receiver,
                values,
                environment,
            ) {
                block_result = callback;
                (type_, UntypedOrigin::FallbackCall)
            } else if let Some((type_, callback)) = super::builtins::transfer_builtin_call(
                analyzer,
                &input,
                &dispatch_receiver,
                &call_arguments,
                values,
                environment,
            ) {
                block_result = callback;
                (type_, UntypedOrigin::FallbackCall)
            } else {
                return Err(format!(
                    "receiver call `{}` on `{dispatch_receiver}` has no method, collection, or builtin contract",
                    input.name.as_str()
                ));
            }
        }
    };
    let type_ = if input.safe_navigation && !receiver_type.is_any() {
        Type::union([Type::Nil, type_])
    } else {
        type_
    };
    let call_can_return = !type_.is_never();
    let raise_type = if call_can_return {
        Type::Never
    } else {
        super::calls::cfg_call_raise_type(analyzer, &input, &receiver_type, environment, &type_)
    };
    let has_normal_path = call_can_return
        && block_result
            .as_ref()
            .is_none_or(|result| result.normal_type.is_some());
    let callback_outcomes = block_result
        .as_ref()
        .map_or_else(OutcomeTypes::default, Eval::callback_outcomes);
    let normal_type = has_normal_path.then_some(type_.clone());
    let mut result = Eval::from_parts(
        normal_type,
        callback_outcomes.join(&OutcomeTypes::for_kind(FlowKind::Raise, raise_type)),
        if has_normal_path {
            Flow::normal()
        } else if !call_can_return {
            Flow::abrupt(FlowKind::Raise)
        } else {
            Flow::empty()
        },
    );
    result.flow = result.flow.union(result.abrupt.flow());
    if let Some(normal_type) = result.normal_type.take() {
        let normal_type = if input.defer_inline_assertion {
            normal_type
        } else {
            analyzer.apply_inline_assertion_in_environment_at(input.site, normal_type, environment)
        };
        result = Eval::from_parts(Some(normal_type), result.abrupt, result.flow);
    }
    analyzer.remember_untyped_origin_at(input.site, &result.type_, untyped_origin);
    Ok(result)
}

pub(super) fn transfer_callable_call(
    analyzer: &mut Analyzer<'_>,
    site: SourceSite,
    receiver: &Type,
    arguments: &super::super::CallArguments<'_>,
) -> Option<Type> {
    match receiver {
        Type::Proc(_, _) | Type::BoundProc { .. } => {
            let (parameters, result) = proc_parts(receiver)?;
            for (index, (actual, expected)) in
                arguments.argument_types.iter().zip(parameters).enumerate()
            {
                if !analyzer.is_assignable(actual, expected) {
                    let argument_site =
                        arguments.argument_sites.get(index).copied().unwrap_or(site);
                    analyzer.error_at(
                        argument_site,
                        format!(
                            "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                        ),
                    );
                }
            }
            Some(result.clone())
        }
        Type::Union(members)
            if members.iter().all(|member| {
                member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
            }) =>
        {
            let mut result = Type::Never;
            for member in members {
                if !member.is_nil() {
                    result =
                        result.join(&transfer_callable_call(analyzer, site, member, arguments)?);
                }
            }
            Some(if result.is_never() { Type::Any } else { result })
        }
        _ => None,
    }
}

pub(super) fn cfg_call_raise_type(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    receiver_type: &Type,
    environment: &Environment,
    return_type: &Type,
) -> Type {
    if !return_type.is_never() {
        return Type::Never;
    }
    if matches!(&input.receiver, cfg::ReceiverOperand::Implicit) {
        return match input.name.as_str() {
            "exit" | "exit!" | "abort" => Type::named("SystemExit"),
            "raise" | "fail" => Type::named("RuntimeError"),
            _ => Type::Never,
        };
    }
    let key = match &input.receiver {
        cfg::ReceiverOperand::Super => environment
            .method_key
            .as_ref()
            .and_then(|current| analyzer.super_method_key(current)),
        cfg::ReceiverOperand::Value(_) => {
            analyzer.receiver_method_key(None, receiver_type, input.name.as_str(), environment)
        }
        cfg::ReceiverOperand::Yield | cfg::ReceiverOperand::Implicit => None,
    };
    key.and_then(|key| analyzer.resolve_method_key(&key))
        .and_then(|key| analyzer.declarations.methods.get(&key))
        .and_then(|state| state.raise_type.clone())
        .filter(|type_| !type_.is_never())
        .unwrap_or_else(|| Type::named("StandardError"))
}
