//! Context-sensitive dispatch for owned CFG calls.
//!
//! Explicit receiver dispatch lives in `dispatch.rs`. These calls instead
//! depend on the enclosing method context: `super` resolves the parent
//! method, while an implicit call first checks parser-independent global
//! contracts and then the current method's owner.

use super::super::{Analyzer, CallArguments, Environment, Eval, OwnedCallInput, UntypedOrigin};
use crate::types::Type;

pub(super) struct ContextTransfer {
    pub(super) type_: Type,
    pub(super) block_result: Option<Eval>,
    pub(super) untyped_origin: UntypedOrigin,
}

pub(super) fn transfer_super_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
) -> Result<ContextTransfer, String> {
    let current_method = environment
        .method_key
        .as_ref()
        .ok_or_else(|| "super call has no enclosing method".to_owned())?;
    let key = analyzer
        .super_method_key(current_method)
        .ok_or_else(|| "super call has no resolvable parent method".to_owned())?;
    analyzer.record_method_dependency(&key, environment);
    let Some(signature) = analyzer
        .observe_call(&key, arguments, input.block.is_some())
        .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
    else {
        return Ok(ContextTransfer {
            type_: Type::Any,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    };
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
        input.name.as_str(),
        &signature,
        arguments,
        Some(receiver),
        block_return_type.as_ref(),
    );
    let untyped_origin = analyzer
        .resolve_method_key(&key)
        .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
        .is_some_and(|state| state.explicit)
        .then_some(UntypedOrigin::DeclaredSignature)
        .unwrap_or(UntypedOrigin::InferredMethod);
    Ok(ContextTransfer {
        type_,
        block_result,
        untyped_origin,
    })
}

pub(super) fn transfer_implicit_call(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    receiver: &Type,
    arguments: &CallArguments<'_>,
    values: &[Option<Type>],
    environment: &mut Environment,
) -> Result<ContextTransfer, String> {
    if let Some(type_) = analyzer.global_call_type(input.name.as_str(), &arguments.argument_types) {
        return Ok(ContextTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
        });
    }

    let key = analyzer.implicit_method_key(input.name.as_str(), environment);
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
            input.name.as_str(),
            &signature,
            arguments,
            Some(receiver),
            block_return_type.as_ref(),
        );
        let untyped_origin = analyzer
            .resolve_method_key(&key)
            .and_then(|resolved| analyzer.declarations.methods.get(&resolved))
            .is_some_and(|state| state.explicit)
            .then_some(UntypedOrigin::DeclaredSignature)
            .unwrap_or(UntypedOrigin::InferredMethod);
        return Ok(ContextTransfer {
            type_,
            block_result,
            untyped_origin,
        });
    }
    if let Some(type_) = analyzer.cfg_passed_dynamic_method_type(input, receiver, environment) {
        return Ok(ContextTransfer {
            type_,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
        });
    }
    Err(format!(
        "implicit call `{}` has no method or owned dynamic-method contract",
        input.name.as_str()
    ))
}
