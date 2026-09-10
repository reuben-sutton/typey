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
    let current_method = environment
        .method_key
        .as_ref()
        .ok_or_else(|| "super call has no enclosing method".to_owned())?;
    let Some(key) = analyzer.super_method_key(current_method) else {
        // Ruby permits a `super` call whose parent method is not present in
        // the available source/RBI set. The recursive evaluator keeps this
        // gradual: the call returns `T.untyped`, and an inline block is still
        // visited with an unknown positional contract. Preserve that behavior
        // in owned CFG transfer instead of abandoning the whole enclosing
        // body merely because the parent declaration is unavailable.
        let block_result = match input.block.as_ref() {
            Some(cfg::BlockOperand::Inline(closure)) => analyzer.transfer_owned_closure_body(
                *closure,
                &[Type::Any],
                None,
                None,
                environment,
            ),
            Some(cfg::BlockOperand::Passed(_)) | None => None,
        };
        return Ok(ContextTransfer {
            type_: Type::Any,
            block_result,
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
            block_result: transfer_inline_block_without_contract(analyzer, input, environment),
            untyped_origin: UntypedOrigin::FallbackCall,
        });
    };
    let block_result = analyzer
        .cfg_block_return_type(
            input,
            &key,
            &signature,
            arguments,
            receiver,
            values,
            environment,
        )
        .or_else(|| transfer_inline_block_without_contract(analyzer, input, environment));
    let block_return_type = block_result.as_ref().map(Analyzer::block_value_type);
    let type_ = analyzer.invoke_signature_at(
        input.site,
        input.name.as_str(),
        &signature,
        arguments,
        Some(receiver),
        block_return_type.as_ref(),
    );
    let type_ = analyzer.widen_recursive_call_return(&key, type_, environment);
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
            // Structural global contracts such as Kernel#each and
            // Kernel#to_enum do not carry a callback signature. Ruby still
            // type-checks an inline block supplied to them, so preserve the
            // owned traversal even though the call result is known here.
            block_result: transfer_inline_block_without_contract(analyzer, input, environment),
            untyped_origin: UntypedOrigin::Propagated,
        });
    }

    if let Some(signature) =
        analyzer.random_formatter_signature(None, receiver, input.name.as_str())
    {
        let type_ = analyzer.invoke_signature_at(
            input.site,
            input.name.as_str(),
            &signature,
            arguments,
            Some(receiver),
            None,
        );
        return Ok(ContextTransfer {
            type_,
            block_result: transfer_inline_block_without_contract(analyzer, input, environment),
            untyped_origin: UntypedOrigin::InferredMethod,
        });
    }

    let key = analyzer.implicit_method_key(input.name.as_str(), environment);
    if matches!(
        &environment.self_type,
        Type::Union(_) | Type::Intersection(_)
    ) && analyzer.resolve_method_key(&key).is_none()
    {
        // A mixin body can be evaluated with a union-valued implicit `self`.
        // The recursive evaluator dispatches that call member-by-member;
        // using the synthetic owner key here would incorrectly turn valid
        // included methods into a whole-body fallback.
        let receiver_type = environment.self_type.clone();
        let result = super::dispatch::transfer_receiver_call(
            analyzer,
            input,
            &receiver_type,
            arguments,
            values,
            environment,
            None,
        )?;
        return Ok(ContextTransfer {
            type_: result.type_,
            block_result: result.block_result,
            untyped_origin: result.untyped_origin,
        });
    }
    analyzer.record_method_dependency(&key, environment);
    if let Some(signature) = analyzer
        .observe_call(&key, arguments, input.block.is_some())
        .map(|signature| analyzer.widen_overridable_noreturn(&key, signature))
    {
        let block_result = analyzer
            .cfg_block_return_type(
                input,
                &key,
                &signature,
                arguments,
                receiver,
                values,
                environment,
            )
            .or_else(|| transfer_inline_block_without_contract(analyzer, input, environment));
        let block_return_type = block_result.as_ref().map(Analyzer::block_value_type);
        let type_ = analyzer.invoke_signature_at(
            input.site,
            input.name.as_str(),
            &signature,
            arguments,
            Some(receiver),
            block_return_type.as_ref(),
        );
        let type_ = analyzer.widen_recursive_call_return(&key, type_, environment);
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

    // An unresolved implicit call is a gradual call, not an unsupported CFG
    // operation. The recursive evaluator reports it when the file is typed
    // strictly and otherwise continues with `T.untyped`; keep visiting an
    // inline block with an unknown contract so the enclosing body can remain
    // on the owned path.
    analyzer.report_missing_method_if_needed_at(input.site, receiver, input.name.as_str(), false);
    let block_result = transfer_inline_block_without_contract(analyzer, input, environment);
    Ok(ContextTransfer {
        type_: Type::Any,
        block_result,
        untyped_origin: UntypedOrigin::FallbackCall,
    })
}

fn transfer_inline_block_without_contract(
    analyzer: &mut Analyzer<'_>,
    input: &OwnedCallInput,
    environment: &mut Environment,
) -> Option<Eval> {
    // `sig { ... }` is a declaration block. Its calls describe a method
    // signature during registration and are not a runtime callback that the
    // CFG should evaluate as Ruby expressions.
    if input.name.as_str() == "sig" {
        return None;
    }
    match input.block.as_ref() {
        Some(cfg::BlockOperand::Inline(closure)) => {
            analyzer.transfer_owned_closure_body(*closure, &[Type::Any], None, None, environment)
        }
        Some(cfg::BlockOperand::Passed(_)) | None => None,
    }
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
