//! Context-sensitive dispatch for owned CFG calls.
//!
//! Explicit receiver dispatch lives in `dispatch.rs`. These calls instead
//! depend on the enclosing method context: `super` resolves the parent
//! method, while an implicit call first checks parser-independent global
//! contracts and then the current method's owner.

use super::super::{Analyzer, CallArguments, Environment, Eval, OwnedCallInput, UntypedOrigin};
use crate::cfg;
use crate::hir;
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
    let Some(current_method) = environment.method_key.as_ref() else {
        return Ok(ContextTransfer {
            type_: Type::Any,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    };
    let Some(key) = analyzer.super_method_key(current_method) else {
        // An isolated component can contain a valid `super` call whose parent
        // declaration is outside the loaded workspace. Preserve the same
        // gradual result as the recursive evaluator, but do not discard the
        // rest of an otherwise representable CFG body.
        return Ok(ContextTransfer {
            type_: Type::Any,
            block_result: None,
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    };
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
    if matches!(input.name.as_str(), "include" | "prepend" | "extend") {
        if let Some(module_name) = owned_mixin_module_name(analyzer, input, environment) {
            analyzer.observe_mixin_hook_owned(
                input.site,
                module_name,
                receiver,
                environment,
                input.name.as_str() == "extend",
            );
        }
        return Ok(ContextTransfer {
            type_: Type::Nil,
            block_result: None,
            untyped_origin: UntypedOrigin::Propagated,
        });
    }
    if matches!(input.name.as_str(), "lambda" | "proc") {
        if let Some(cfg::BlockOperand::Inline(closure)) = input.block.as_ref() {
            let type_ = analyzer
                .cfg_owned_closure_type(*closure, environment)
                .ok_or_else(|| "proc/lambda closure transfer failed".to_owned())?;
            return Ok(ContextTransfer {
                type_,
                block_result: None,
                untyped_origin: UntypedOrigin::Propagated,
            });
        }
    }
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

pub(super) fn owned_mixin_module_name(
    analyzer: &Analyzer<'_>,
    input: &OwnedCallInput,
    environment: &Environment,
) -> Option<String> {
    let expression = input.expression?;
    let hir::ExprKind::Call(call) = &analyzer.program.hir_program.expression(expression)?.kind
    else {
        return None;
    };
    let value = call.arguments.iter().find_map(|argument| match argument {
        hir::Argument::Positional(value) => Some(*value),
        _ => None,
    })?;
    let hir::ExprKind::Read(hir::Read::Constant(path)) =
        &analyzer.program.hir_program.expression(value)?.kind
    else {
        return None;
    };
    Some(analyzer.resolve_name(
        path.as_str(),
        analyzer.lexical_owner(environment).as_deref(),
    ))
}
