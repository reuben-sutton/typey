//! Owned shapes used at the boundary between Ruby call syntax and dispatch.
//!
//! Owned call shapes and callback contracts consumed by CFG transfer.

use super::{
    optional_proc_type, proc_parts, Analyzer, Eval, MethodKey, PredicateAlias, SourceSite,
};
use crate::cfg;
use crate::hir;
use crate::signature::MethodSig;
use crate::types::Type;
use ruby_prism::Node;

/// The owned semantic input consumed by CFG call transfer.
#[derive(Clone, Copy, Debug)]
pub(super) struct OwnedCallInput<'a> {
    pub(super) site: SourceSite,
    pub(super) expression: Option<hir::ExprId>,
    pub(super) receiver: &'a cfg::ReceiverOperand,
    pub(super) name: &'a hir::Name,
    pub(super) arguments: &'a [cfg::ArgumentOperand],
    pub(super) block: Option<&'a cfg::BlockOperand>,
    pub(super) safe_navigation: bool,
    pub(super) defer_inline_assertion: bool,
}

impl<'a> OwnedCallInput<'a> {
    pub(super) fn from_operation(operation: &'a cfg::Operation) -> Option<Self> {
        let cfg::OperationKind::Call {
            receiver,
            name,
            arguments,
            block,
            safe_navigation,
        } = &operation.kind
        else {
            return None;
        };
        Some(Self {
            site: SourceSite::from_span(operation.span, operation.expression),
            expression: operation.expression,
            receiver,
            name,
            arguments,
            block: block.as_ref(),
            safe_navigation: *safe_navigation,
            defer_inline_assertion: operation.defer_inline_assertion,
        })
    }

    pub(super) fn new(
        site: SourceSite,
        expression: Option<hir::ExprId>,
        receiver: &'a cfg::ReceiverOperand,
        name: &'a hir::Name,
        arguments: &'a [cfg::ArgumentOperand],
        block: Option<&'a cfg::BlockOperand>,
        safe_navigation: bool,
        defer_inline_assertion: bool,
    ) -> Self {
        Self {
            site,
            expression,
            receiver,
            name,
            arguments,
            block,
            safe_navigation,
            defer_inline_assertion,
        }
    }
}

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_yield_result(
        &mut self,
        site: SourceSite,
        arguments: &CallArguments<'_>,
        environment: &mut super::Environment,
    ) -> Option<Type> {
        let Some(key) = environment.method_key.clone() else {
            // The parser already reports an invalid top-level/class-body
            // yield. Keep the owned CFG body executable so later statements
            // are still checked; there is no block contract to infer here.
            return Some(Type::Any);
        };
        let (expected, return_type) = {
            let Some(state) = self.declarations.methods.get(&key) else {
                // A namespace body is not a method and therefore has no
                // yielded-block signature. This is an invalid-yield case,
                // not a reason to hand the enclosing body back to Prism.
                return Some(Type::Any);
            };
            let expected = state
                .block
                .as_ref()
                .and_then(optional_proc_type)
                .and_then(|block| proc_parts(&block).map(|(parameters, _)| parameters.to_vec()));
            let return_type = state.block_return_type.clone().unwrap_or(Type::Any);
            (expected, return_type)
        };
        if let Some(expected) = expected.as_ref() {
            for (index, actual) in arguments.argument_types.iter().enumerate() {
                if let Some(expected) = expected.get(index) {
                    if !self.is_assignable(actual, expected) {
                        let argument_site =
                            arguments.argument_sites.get(index).copied().unwrap_or(site);
                        if let Some(argument) = arguments.argument_nodes.get(index) {
                            self.error(
                                argument,
                                format!(
                                    "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                                ),
                            );
                        } else {
                            self.error_at(
                                argument_site,
                                format!(
                                    "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                                ),
                            );
                        }
                    }
                }
            }
        }
        if let Some(state) = self.declarations.methods.get_mut(&key) {
            if state.observe_yield_arguments(&arguments.argument_types) {
                self.fixpoint.changed_methods.insert(key);
            }
        }
        Some(return_type)
    }

    pub(super) fn cfg_block_return_type<'node>(
        &mut self,
        input: &OwnedCallInput,
        key: &MethodKey,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: &Type,
        values: &[Option<Type>],
        environment: &mut super::Environment,
    ) -> Option<Eval> {
        match input.block.as_ref()? {
            cfg::BlockOperand::Inline(closure) => self.cfg_inline_block_return_type(
                input,
                *closure,
                key,
                signature,
                arguments,
                receiver_type,
                environment,
            ),
            cfg::BlockOperand::Passed(value) => {
                let mut bindings = self.infer_type_parameter_bindings(signature, arguments, None);
                bindings.extend(self.infer_generic_member_bindings(
                    signature,
                    arguments,
                    Some(receiver_type),
                ));
                // A block result can be the only source of a generic method
                // binding.  When it is not inferable at this call site,
                // Sorbet treats the callback result contract as open rather
                // than exposing the method's symbolic `U` in a diagnostic.
                for parameter in &signature.type_parameters {
                    bindings.entry(parameter.clone()).or_insert(Type::Anything);
                }
                let expected =
                    signature
                        .block
                        .as_ref()
                        .and_then(optional_proc_type)
                        .map(|expected| {
                            self.substitute_signature_type(
                                &expected,
                                Some(receiver_type),
                                &bindings,
                                &signature.type_parameters,
                            )
                        });
                if let (Some(expected), Some(name)) =
                    (expected.as_ref(), self.cfg_passed_symbol_name(input))
                {
                    let result = self.eval_owned_symbol_passed_block_named(
                        input.site,
                        &name,
                        expected,
                        environment,
                    )?;
                    return Some(Eval::value(result));
                }
                let actual = values.get(value.0 as usize).cloned().flatten()?;
                let block_site = self.cfg_passed_block_site(input).unwrap_or(input.site);
                let local_name = self.cfg_passed_block_local_name(input);
                let passed_signature = optional_proc_type(&actual)
                    .and_then(|block| Self::passed_block_signature(&block));
                let forwarded_signature = local_name.as_deref().and_then(|name| {
                    let expected_parameters = expected
                        .as_ref()
                        .and_then(|expected| proc_parts(expected))
                        .map(|(parameters, _)| parameters.to_vec())?;
                    self.forwarded_block_signature(name, &actual, &expected_parameters, environment)
                });
                let effective_signature =
                    forwarded_signature.as_ref().or(passed_signature.as_ref());
                if let (Some(expected), Some(actual_signature)) =
                    (expected.as_ref(), effective_signature)
                {
                    if !Self::passed_block_is_assignable(self, actual_signature, expected) {
                        self.error_at(
                            block_site,
                            format!(
                                "Expected `{}` but found `{}` for block argument",
                                Self::block_type_description(expected),
                                Self::block_type_description(actual_signature),
                            ),
                        );
                    }
                }
                let result = effective_signature
                    .and_then(|block| proc_parts(block).map(|(_, result)| result.clone()))
                    .map(Eval::value)
                    .or_else(|| {
                        let name = local_name.as_deref()?;
                        let expected_parameters = expected
                            .as_ref()
                            .and_then(|expected| proc_parts(expected))
                            .map(|(parameters, _)| parameters.to_vec())?;
                        let signature = self.forwarded_block_signature(
                            name,
                            &actual,
                            &expected_parameters,
                            environment,
                        )?;
                        proc_parts(&signature).map(|(_, result)| Eval::value(result.clone()))
                    });
                if let Some(block_result) = result.as_ref().map(Self::block_value_type) {
                    let provisional = self.cfg_passed_block_is_provisional(input, environment);
                    self.observe_cfg_block_return(&key, &block_result, provisional);
                }
                result
            }
        }
    }

    fn cfg_passed_block_is_provisional(
        &self,
        input: &OwnedCallInput,
        environment: &super::Environment,
    ) -> bool {
        let Some(expression) = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))
        else {
            return false;
        };
        let hir::ExprKind::Call(call) = &expression.kind else {
            return false;
        };
        let Some(hir::BlockArgument::Passed(block)) = call.block.as_ref() else {
            return false;
        };
        let Some(hir::ExprKind::Read(hir::Read::Local(local))) = self
            .program
            .hir_program
            .expression(*block)
            .map(|expression| &expression.kind)
        else {
            return false;
        };
        let Some(name) = self.program.hir_program.local_name(*local) else {
            return false;
        };
        environment.is_provisional(name.as_str())
    }

    fn observe_cfg_block_return(
        &mut self,
        key: &MethodKey,
        block_result: &Type,
        provisional: bool,
    ) {
        let Some(key) = self.resolve_method_key(key) else {
            return;
        };
        if self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| !state.explicit)
            && self
                .declarations
                .methods
                .get_mut(&key)
                .is_some_and(|state| {
                    if provisional {
                        state.observe_provisional_block_return(block_result)
                    } else {
                        state.observe_forwarded_block_return(block_result)
                    }
                })
        {
            self.fixpoint.changed_methods.insert(key);
        }
    }

    /// Evaluate a callback whose contract comes from a parser-free structural
    /// model rather than an RBI declaration. Collection methods are the main
    /// user of this path: their generic block contract is known even when the
    /// core RBI has no usable method signature.
    pub(super) fn cfg_owned_block_return_type(
        &mut self,
        input: &OwnedCallInput,
        expected_parameters: &[Type],
        expected_return: &Type,
        values: &[Option<Type>],
        environment: &mut super::Environment,
    ) -> Option<Eval> {
        self.cfg_owned_block_return_type_with_environment(
            input,
            expected_parameters,
            expected_return,
            values,
            environment,
        )
        .map(|(result, _)| result)
    }

    /// As [`cfg_owned_block_return_type`], but retain the callback's local
    /// environment.  This matters for callbacks whose contract mutates a
    /// block parameter, such as `each_with_object`: the callback result is
    /// not the collection result, so callers need the post-callback binding
    /// to recover the refined accumulator type.
    pub(super) fn cfg_owned_block_return_type_with_environment(
        &mut self,
        input: &OwnedCallInput,
        expected_parameters: &[Type],
        expected_return: &Type,
        values: &[Option<Type>],
        environment: &mut super::Environment,
    ) -> Option<(Eval, super::Environment)> {
        let block_site = self.cfg_passed_block_site(input).unwrap_or(input.site);
        let expected = Type::Proc(
            expected_parameters.to_vec(),
            Box::new(expected_return.clone()),
        );
        match input.block.as_ref()? {
            cfg::BlockOperand::Inline(closure) => {
                // Collection callbacks with a literal pair result need to
                // retain the fixed shape for consumers such as `to_h`.
                // Legacy collection transfer derives this expectation from
                // the block body; do the same here when the structural
                // contract intentionally leaves the callback result open.
                let literal_return = matches!(expected_return, Type::Anything)
                    .then(|| {
                        super::owned_blocks::owned_literal_block_tuple_type(
                            &self.program.hir_program,
                            *closure,
                        )
                    })
                    .flatten();
                let expected_return = literal_return.as_ref().unwrap_or(expected_return);
                self.transfer_owned_closure_body_with_environment(
                    *closure,
                    expected_parameters,
                    Some(expected_return),
                    None,
                    environment,
                )
            }
            cfg::BlockOperand::Passed(value) => {
                let actual = values.get(value.0 as usize).cloned().flatten()?;
                if actual.is_nil() {
                    // `&nil` is Ruby's spelling for omitting a block.
                    return None;
                }
                if let Some(name) = self.cfg_passed_symbol_name(input) {
                    let result = self.eval_owned_symbol_passed_block_named(
                        block_site,
                        &name,
                        &expected,
                        environment,
                    )?;
                    return Some((Eval::value(result), environment.clone()));
                }
                let local_name = self.cfg_passed_block_local_name(input);
                let Some(signature) = Self::passed_block_signature(&actual) else {
                    if let Some(local_name) = local_name {
                        if let Some(signature) = self.forwarded_block_signature(
                            &local_name,
                            &actual,
                            expected_parameters,
                            environment,
                        ) {
                            let result = proc_parts(&signature)
                                .map_or(Type::Any, |(_, result)| result.clone());
                            return Some((Eval::value(result), environment.clone()));
                        }
                    }
                    // An ordinary unannotated Proc still has no callback
                    // contract. Preserve the gradual result in that case;
                    // only a marked `&block` parameter is eligible for the
                    // forwarding rule above.
                    return Some((Eval::value(Type::Any), environment.clone()));
                };
                let forwarded_signature = local_name.as_deref().and_then(|name| {
                    self.forwarded_block_signature(name, &actual, expected_parameters, environment)
                });
                let effective_signature = forwarded_signature.as_ref().unwrap_or(&signature);
                if !Self::passed_block_is_assignable(self, effective_signature, &expected) {
                    self.error_at(
                        block_site,
                        format!(
                            "Expected `{}` but found `{}` for block argument",
                            Self::block_type_description(&expected),
                            Self::block_type_description(effective_signature),
                        ),
                    );
                }
                let result =
                    proc_parts(effective_signature).map_or(Type::Any, |(_, result)| result.clone());
                Some((Eval::value(result), environment.clone()))
            }
        }
    }

    fn cfg_passed_block_site(&self, input: &OwnedCallInput) -> Option<SourceSite> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::BlockArgument::Passed(block) = call.block.as_ref()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*block)?;
        let mut start = expression.span.start as usize;
        if start > 0 && self.program.source.get(start - 1) == Some(&b'&') {
            start -= 1;
        }
        Some(SourceSite::new(start, expression.span.end as usize))
    }

    fn cfg_passed_symbol_name(&self, input: &OwnedCallInput) -> Option<String> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::BlockArgument::Passed(block) = call.block.as_ref()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*block)?;
        match &expression.kind {
            hir::ExprKind::Literal(hir::Literal::Symbol(name)) => Some(name.clone()),
            _ => None,
        }
    }

    fn cfg_passed_block_local_name(&self, input: &OwnedCallInput) -> Option<String> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::BlockArgument::Passed(block) = call.block.as_ref()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*block)?;
        let hir::ExprKind::Read(hir::Read::Local(local)) = &expression.kind else {
            return None;
        };
        self.program
            .hir_program
            .local_name(*local)
            .map(|name| name.as_str().to_owned())
    }

    pub(super) fn cfg_dynamic_instance_variable_name(
        &self,
        input: &OwnedCallInput,
    ) -> Option<String> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::Argument::Positional(argument) = call.arguments.first()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*argument)?;
        let name = match &expression.kind {
            hir::ExprKind::Literal(hir::Literal::Symbol(name)) => name.clone(),
            // HIR string literals retain their source spelling. Dynamic ivar
            // APIs conventionally receive symbols, but accept the ordinary
            // quoted-string form as well when it is statically known.
            hir::ExprKind::Literal(hir::Literal::String(name)) => name
                .strip_prefix('"')
                .and_then(|name| name.strip_suffix('"'))
                .or_else(|| {
                    name.strip_prefix('\'')
                        .and_then(|name| name.strip_suffix('\''))
                })
                .map(str::to_owned)?,
            _ => return None,
        };
        name.starts_with('@').then_some(name)
    }
}

pub(super) struct KeywordArgument<'node> {
    pub(super) name: String,
    pub(super) node: Option<Node<'node>>,
    pub(super) site: SourceSite,
    pub(super) type_: Type,
}

#[derive(Default)]
pub(super) struct CallArguments<'node> {
    pub(super) argument_nodes: Vec<Node<'node>>,
    pub(super) argument_sites: Vec<SourceSite>,
    pub(super) argument_types: Vec<Type>,
    pub(super) argument_aliases: Vec<Option<PredicateAlias>>,
    /// Owned CFG calls retain the precise tuple shape of fixed literal-array
    /// arguments separately from their ordinary array type.  Signature
    /// checking can use it when the callee expects a tuple without making
    /// every array literal globally tuple-shaped.
    pub(super) literal_tuple_arguments: Vec<Option<Type>>,
    pub(super) argument_indices: Vec<usize>,
    pub(super) positional_indices: Vec<usize>,
    pub(super) positional_types: Vec<Type>,
    pub(super) keyword_arguments: Vec<KeywordArgument<'node>>,
    pub(super) keyword_hash_indices: Vec<usize>,
    pub(super) has_keyword_splat: bool,
    pub(super) has_dynamic_positional_splat: bool,
    pub(super) dynamic_positional_splat_types: Vec<Type>,
    pub(super) has_dynamic_keyword_splat: bool,
    pub(super) has_unknown_positional_splat: bool,
    pub(super) has_unknown_keyword_splat: bool,
    /// The call uses Ruby's `...` forwarding form. There is no concrete
    /// argument list at this syntax site; it is the caller's complete
    /// positional, keyword, and block argument set.
    pub(super) forwards_arguments: bool,
    /// For mixed calls such as `target(value, ...)`, the prefix before this
    /// positional index is concrete and may still contribute inference. The
    /// forwarded suffix remains opaque for arity and contract checking.
    pub(super) forwarded_positional_start: Option<usize>,
    /// The call forwards keyword arguments as well as its positional tail.
    pub(super) forwards_keywords: bool,
}
