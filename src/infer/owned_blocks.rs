//! Owned callback-block contracts used by CFG call transfer.
//!
//! The recursive evaluator observes inline blocks from Prism nodes. CFG
//! transfer has the same information in HIR: a closure id, its parameters,
//! body, and source span. Keeping this contract here prevents `infer.rs` and
//! `cfg_transfer.rs` from growing another parser-shaped callback adapter.

use super::{
    optional_proc_type, proc_parts, Analyzer, CallArguments, Environment, Eval, MethodKey,
    MethodState, OwnedCallInput, SourceSite,
};
use crate::hir;
use crate::signature::MethodSig;
use crate::types::Type;

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_inline_block_return_type<'node>(
        &mut self,
        input: &OwnedCallInput,
        closure_id: hir::ClosureId,
        key: &MethodKey,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: &Type,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let key = self.resolve_method_key(key)?;
        if matches!(
            key.name.as_str(),
            "define_method" | "define_singleton_method"
        ) {
            // These APIs consume the block as a future method body. Their
            // receiver and parameter contract is not an ordinary callback
            // contract, so keep the migration boundary transactional.
            return None;
        }

        let mut bindings = self.infer_type_parameter_bindings(signature, arguments, None);
        bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            Some(receiver_type),
        ));
        let previous_substitution_context = self.substitution_context.replace(key.clone());
        let block_signature = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                Some(receiver_type),
                &bindings,
                &signature.type_parameters,
            )
        });
        self.substitution_context = previous_substitution_context;

        let expected = block_signature
            .as_ref()
            .and_then(optional_proc_type)
            .and_then(|block| proc_parts(&block).map(|(parameters, _)| parameters.to_vec()))
            .unwrap_or_else(|| {
                self.declarations
                    .methods
                    .get(&key)
                    .map_or_else(Vec::new, MethodState::block_parameters)
            });
        let expected_return = block_signature
            .as_ref()
            .and_then(optional_proc_type)
            .and_then(|block| proc_parts(&block).map(|(_, result)| result.clone()));

        let class_new_receiver = (key.name == "new"
            && key.singleton
            && key
                .owner
                .as_deref()
                .is_some_and(|owner| super::name_matches(owner, "Class")))
        .then(|| {
            arguments
                .argument_types
                .first()
                .filter(|argument| Self::class_object_instance_type(argument).is_some())
                .cloned()
        })
        .flatten();
        let binds_block_to_receiver = self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| state.binds_block_to_receiver);
        let bound_receiver = class_new_receiver
            .or_else(|| self.active_support_test_block_receiver(&key, Some(receiver_type)))
            .or_else(|| {
                block_signature
                    .as_ref()
                    .and_then(optional_proc_type)
                    .and_then(|block| super::proc_receiver(&block).cloned())
            })
            .or_else(|| {
                binds_block_to_receiver
                    .then(|| Self::class_object_instance_type(receiver_type))
                    .flatten()
            })
            .or_else(|| self.rails_initializer_block_receiver(&key, Some(receiver_type)))
            .or_else(|| self.rails_application_configure_block_receiver(&key, Some(receiver_type)))
            .or_else(|| self.rails_route_draw_block_receiver(&key, Some(receiver_type)))
            .or_else(|| self.active_support_ci_block_receiver(&key, Some(receiver_type)));

        let block_result = match self.transfer_owned_closure_body(
            closure_id,
            &expected,
            expected_return.as_ref(),
            bound_receiver.as_ref(),
            environment,
        ) {
            Some(block_type) => block_type,
            None => return None,
        };
        let block_type = Self::block_value_type(&block_result);
        let closure_site = self
            .hir_program
            .closure(closure_id)
            .map(|closure| SourceSite::from_span(closure.span, None))
            .unwrap_or(input.site);

        let mut checked_bindings =
            self.infer_type_parameter_bindings(signature, arguments, Some(&block_type));
        checked_bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            Some(receiver_type),
        ));
        let checked_block_signature = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                Some(receiver_type),
                &checked_bindings,
                &signature.type_parameters,
            )
        });
        let checked_expected_return = checked_block_signature
            .as_ref()
            .and_then(optional_proc_type)
            .and_then(|block| proc_parts(&block).map(|(_, result)| result.clone()));
        let explicit = self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| state.explicit);
        if explicit {
            if let Some(expected_return) = checked_expected_return.as_ref() {
                if !expected_return.is_any()
                    && !expected_return.is_nil()
                    && !self.is_assignable(&block_type, expected_return)
                {
                    self.check_assignable_at(closure_site, &block_type, expected_return);
                }
            }
        }
        if self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| !state.explicit)
            && self
                .declarations
                .methods
                .get_mut(&key)
                .is_some_and(|state| state.observe_block_return(&block_type))
        {
            self.fixpoint.changed_methods.insert(key);
        }
        Some(block_result)
    }

    fn transfer_owned_closure_body(
        &mut self,
        closure_id: hir::ClosureId,
        expected: &[Type],
        expected_return: Option<&Type>,
        bound_receiver: Option<&Type>,
        outer: &mut Environment,
    ) -> Option<Eval> {
        let closure = self.hir_program.closure(closure_id)?.clone();
        let captured = outer.clone();
        let mut closure_environment = outer.clone();
        if let Some(receiver) = bound_receiver {
            closure_environment.self_type = match receiver {
                Type::AttachedClassOf(owner) => Type::named(owner.clone()),
                _ => receiver.clone(),
            };
            let class_object_owner = Self::class_object_owner(receiver);
            closure_environment.method_key = Some(MethodKey {
                owner: class_object_owner
                    .clone()
                    .or_else(|| Self::named_type_name(receiver))
                    .or_else(|| outer.method_key.as_ref().and_then(|key| key.owner.clone())),
                name: "<bound-block>".to_owned(),
                singleton: class_object_owner.is_some(),
            });
        }

        bind_owned_parameters(&closure.parameters, expected, &mut closure_environment);
        let previous_expected_return = self.expected_return_type.take();
        self.expected_return_type = expected_return.map(|expected| {
            if matches!(expected, Type::TypeVar(_)) {
                owned_literal_block_tuple_type(&self.hir_program, closure_id)
                    .unwrap_or_else(|| expected.clone())
            } else {
                expected.clone()
            }
        });
        let body_result = self.eval_cfg_body_owned(
            SourceSite::from_span(closure.span, None),
            closure.body,
            &mut closure_environment,
            false,
        );
        self.expected_return_type = previous_expected_return;
        let body_result = body_result?;
        self.propagate_block_locals(outer, &captured, &closure_environment);
        Some(body_result)
    }
}

fn owned_literal_block_tuple_type(
    program: &hir::Program,
    closure_id: hir::ClosureId,
) -> Option<Type> {
    let closure = program.closure(closure_id)?;
    let body = program.body(closure.body)?;
    let expression = program.expression(body.root)?;
    let array = match &expression.kind {
        hir::ExprKind::Array(elements) => elements,
        hir::ExprKind::Sequence(expressions) => {
            let expression = expressions
                .last()
                .and_then(|expression| program.expression(*expression))?;
            let hir::ExprKind::Array(elements) = &expression.kind else {
                return None;
            };
            elements
        }
        _ => return None,
    };
    array
        .iter()
        .all(|element| matches!(element, hir::ArrayElement::Value(_)))
        .then(|| Type::Tuple(vec![Type::Any; array.len()]))
}

fn bind_owned_parameters(
    parameters: &hir::Parameters,
    expected: &[Type],
    environment: &mut Environment,
) {
    let expected = if parameters
        .parameters
        .iter()
        .filter(|parameter| parameter.kind == hir::ParameterKind::Required)
        .count()
        > 1
    {
        if let [Type::Tuple(elements)] = expected {
            elements.as_slice()
        } else {
            expected
        }
    } else {
        expected
    };
    let mut positional_index = 0;
    for parameter in &parameters.parameters {
        let type_ = match parameter.kind {
            hir::ParameterKind::Required
            | hir::ParameterKind::Optional
            | hir::ParameterKind::Post => {
                let type_ = expected.get(positional_index).cloned().unwrap_or(Type::Any);
                positional_index += 1;
                type_
            }
            hir::ParameterKind::Rest | hir::ParameterKind::Forwarded => {
                let type_ = expected.get(positional_index).cloned().unwrap_or(Type::Any);
                positional_index += 1;
                Type::Array(Box::new(type_))
            }
            hir::ParameterKind::RequiredKeyword | hir::ParameterKind::OptionalKeyword => Type::Any,
            hir::ParameterKind::KeywordRest => {
                Type::Hash(Box::new(Type::Symbol), Box::new(Type::Any))
            }
            hir::ParameterKind::Block => Type::Proc(Vec::new(), Box::new(Type::Any)),
            hir::ParameterKind::Anonymous => Type::Any,
        };
        if let Some(name) = &parameter.name {
            environment.bind(name.as_str().to_owned(), type_.clone());
        }
        if positional_index == 1 && parameter.name.is_none() {
            environment.bind("it", type_);
        }
    }
}
