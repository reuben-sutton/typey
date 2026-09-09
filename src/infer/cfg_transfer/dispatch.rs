//! Receiver-side dispatch for owned CFG calls.
//!
//! The outer call transfer owns argument materialization and the common
//! normal/abrupt outcome protocol. This layer selects the receiver contract:
//! callable values, declared methods, collection contracts, or primitive
//! builtins. Keeping that choice here makes the dispatch order explicit and
//! leaves the surrounding CFG transfer independent of individual receiver
//! models.

use super::super::{
    proc_parts, Analyzer, CallArguments, Environment, Eval, OwnedCallInput, SourceSite,
    UntypedOrigin,
};
use crate::types::Type;

pub(super) struct ReceiverTransfer {
    pub(super) type_: Type,
    pub(super) block_result: Option<Eval>,
    pub(super) untyped_origin: UntypedOrigin,
}

pub(super) fn transfer_receiver_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
) -> Result<ReceiverTransfer, String> {
    if let Type::Union(members) = receiver {
        // A union receiver has no single method key. Dispatch each concrete
        // member through the same contract order instead of collapsing the
        // whole receiver to a parser-era fallback. Calls with blocks remain
        // outside this path until callback state can be joined per member.
        if input.block.is_none() {
            let mut result_type = Type::Never;
            let mut untyped_origin = UntypedOrigin::Propagated;
            for member in members {
                let result = transfer_receiver_call(
                    analyzer,
                    input,
                    member,
                    arguments,
                    values,
                    environment,
                )?;
                result_type = result_type.join(&result.type_);
                if result.untyped_origin == UntypedOrigin::FallbackCall {
                    untyped_origin = UntypedOrigin::FallbackCall;
                } else if untyped_origin != UntypedOrigin::FallbackCall
                    && result.untyped_origin == UntypedOrigin::DeclaredSignature
                {
                    untyped_origin = UntypedOrigin::DeclaredSignature;
                } else if untyped_origin != UntypedOrigin::FallbackCall
                    && result.untyped_origin == UntypedOrigin::InferredMethod
                    && untyped_origin == UntypedOrigin::Propagated
                {
                    untyped_origin = UntypedOrigin::InferredMethod;
                }
            }
            return Ok(ReceiverTransfer {
                type_: result_type,
                block_result: None,
                untyped_origin,
            });
        }
    }
    let name = input.name.as_str();
    let callable_type = if matches!(name, "call" | "[]") {
        transfer_callable_call(analyzer, input.site, receiver, arguments)
    } else {
        None
    };
    if let Some(type_) = callable_type {
        return Ok(ReceiverTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
        });
    }
    if input.safe_navigation && receiver.is_never() {
        return Ok(ReceiverTransfer {
            type_: Type::Nil,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    }

    if let Some(type_) =
        analyzer.eval_node_helpers_method(receiver, name, &arguments.argument_types)
    {
        return Ok(ReceiverTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::InferredMethod,
        });
    }

    // `[]` is also ordinary Ruby method dispatch. Only proc-like receivers
    // use the callable shorthand; a nominal receiver must still resolve its
    // declared `[]` method here.
    let key = analyzer.receiver_method_key(None, receiver, name, environment);
    if let Some(key) = key {
        analyzer.record_method_dependency(&key, environment);
        if let Some(signature) = analyzer
            .observe_call(&key, arguments, input.block.is_some())
            .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
        {
            let block_result = analyzer.cfg_block_return_type(
                input,
                &key,
                &signature,
                arguments,
                receiver,
                values,
                environment,
            );
            let block_return_type = block_result.as_ref().map(Analyzer::block_value_type);
            let type_ = analyzer.invoke_signature_at(
                input.site,
                name,
                &signature,
                arguments,
                Some(receiver),
                block_return_type.as_ref(),
            );
            let type_ = if name == "new" {
                let type_ = analyzer.instantiate_generic_class(type_);
                analyzer.default_class_constructor_type(receiver, type_)
            } else {
                type_
            };
            let untyped_origin = analyzer
                .resolve_method_key(&key)
                .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
                .is_some_and(|state| state.explicit)
                .then_some(UntypedOrigin::DeclaredSignature)
                .unwrap_or(UntypedOrigin::InferredMethod);
            return Ok(ReceiverTransfer {
                type_,
                block_result,
                untyped_origin,
            });
        }
    }

    if let Some((type_, block_result)) =
        super::collections::transfer_collection_call(analyzer, input, receiver, values, environment)
    {
        return Ok(ReceiverTransfer {
            type_,
            block_result,
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    }
    if let Some((type_, block_result)) = super::builtins::transfer_builtin_call(
        analyzer,
        input,
        receiver,
        arguments,
        values,
        environment,
    ) {
        return Ok(ReceiverTransfer {
            type_,
            block_result,
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    }

    Err(format!(
        "receiver call `{name}` on `{receiver}` has no method, collection, or builtin contract"
    ))
}

pub(super) fn transfer_callable_call(
    analyzer: &mut Analyzer<'_>,
    site: SourceSite,
    receiver: &Type,
    arguments: &CallArguments<'_>,
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
                            "Expected `{expected}` but found `{actual}` for argument `arg{index}"
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
