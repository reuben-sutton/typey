//! Shared call-specific semantics for owned CFG transfer.

use super::super::{proc_parts, Analyzer, Environment, OwnedCallInput, SourceSite};
use crate::cfg;
use crate::types::Type;

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
