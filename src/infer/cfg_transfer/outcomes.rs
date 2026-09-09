//! Outcome assembly for owned CFG calls.
//!
//! Dispatchers return a normal type plus any callback outcome. This layer is
//! the single place that turns those facts into `Eval`, applies safe
//! navigation and inline assertions, and records the raised exception type.

use super::super::{
    Analyzer, Environment, Eval, Flow, FlowKind, OutcomeTypes, OwnedCallInput, UntypedOrigin,
};
use crate::cfg;
use crate::types::Type;

pub(super) fn finish_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver_type: &Type,
    mut type_: Type,
    block_result: Option<Eval>,
    untyped_origin: UntypedOrigin,
    environment: &mut Environment,
) -> Eval {
    if input.safe_navigation && !receiver_type.is_any() {
        type_ = Type::union([Type::Nil, type_]);
    }
    let call_can_return = !type_.is_never();
    let raise_type = if call_can_return {
        Type::Never
    } else {
        cfg_call_raise_type(analyzer, input, receiver_type, environment, &type_)
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
    result
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
            "raise" | "fail" => Type::named("StandardError"),
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
