//! Owned callback-block contracts used by CFG call transfer.
//!
//! The recursive evaluator observes inline blocks from Prism nodes. CFG
//! transfer has the same information in HIR: a closure id, its parameters,
//! body, and source span. Keeping this contract here prevents `infer.rs` and
//! `cfg_transfer.rs` from growing another parser-shaped callback adapter.

use super::{
    method_state::BlockReceiverBinding, optional_proc_type, proc_parts, Analyzer, CallArguments,
    Environment, Eval, MethodKey, MethodState, OwnedCallInput, SourceSite,
};
use crate::cfg;
use crate::hir;
use crate::signature::MethodSig;
use crate::types::Type;

impl<'src> Analyzer<'src> {
    /// Transfer Module/Class declaration DSL calls without requiring the
    /// core RBI to describe every metaprogramming entry point. These calls
    /// are real Ruby sends, but their runtime effect is already represented
    /// by declaration registration or by the owned dynamic-method contract.
    pub(super) fn cfg_declaration_call(
        &mut self,
        input: &OwnedCallInput,
        receiver: &Type,
        _values: &[Option<Type>],
        environment: &mut Environment,
    ) -> Option<(Type, Option<Eval>)> {
        let name = input.name.as_str();
        let is_declaration = matches!(
            name,
            "alias_method"
                | "attr_reader"
                | "attr_writer"
                | "attr_accessor"
                | "private"
                | "protected"
                | "public"
                | "module_function"
                | "private_class_method"
                | "has_attached_class!"
                | "type_member"
                | "type_template"
                | "mixes_in_class_methods"
                | "private_constant"
                | "public_constant"
                | "refine"
        );
        if !is_declaration && !matches!(name, "define_method" | "define_singleton_method") {
            return None;
        }
        let class_object = Self::class_object_instance_type(receiver);
        if class_object.is_none() {
            return None;
        }

        if name == "alias_method" && matches!(input.receiver, cfg::ReceiverOperand::Value(_)) {
            // Explicit class-object calls retain the dispatch-layer alias
            // mutation contract below; implicit class-body `alias_method`
            // calls are handled as declaration DSL.
            return None;
        }

        if matches!(name, "define_method" | "define_singleton_method") {
            let bound_receiver = if name == "define_method" {
                class_object
            } else {
                Some(receiver.clone())
            };
            match input.block.as_ref() {
                Some(cfg::BlockOperand::Inline(closure)) => {
                    let binding = if name == "define_method" {
                        BlockReceiverBinding::Instance
                    } else {
                        BlockReceiverBinding::Receiver
                    };
                    self.observe_cfg_define_method_binding(binding, environment);
                    let _ = self.transfer_owned_closure_body(
                        *closure,
                        &[Type::Any],
                        None,
                        bound_receiver.as_ref(),
                        environment,
                    );
                }
                Some(cfg::BlockOperand::Passed(_)) => {
                    let _ = self.cfg_passed_dynamic_method_type(input, receiver, environment);
                }
                None => {}
            }
            return Some((Type::Symbol, None));
        }

        is_declaration.then_some((Type::Nil, None))
    }

    /// `class_eval`/`module_eval` and their siblings have a block-only Ruby
    /// form that is represented by a separate RBI overload. Dispatching that
    /// overload through ordinary positional arity checking is incorrect: the
    /// block is the operation's input, not an omitted required string. Keep
    /// the dynamic-eval contract beside the owned closure transfer so both
    /// inline and passed blocks use the same bound receiver semantics.
    pub(super) fn cfg_dynamic_eval_call(
        &mut self,
        input: &OwnedCallInput,
        receiver: &Type,
        values: &[Option<Type>],
        environment: &mut Environment,
    ) -> Option<Eval> {
        if !matches!(
            input.name.as_str(),
            "class_eval" | "module_eval" | "class_exec" | "instance_eval"
        ) {
            return None;
        }
        if !matches!(input.name.as_str(), "instance_eval")
            && !receiver.is_any()
            && Self::class_object_instance_type(receiver).is_none()
            && !matches!(
                receiver,
                Type::Named(name, _)
                    if super::name_matches(name, "Class") || super::name_matches(name, "Module")
            )
        {
            return None;
        }
        match input.block.as_ref() {
            Some(cfg::BlockOperand::Inline(closure)) => self.transfer_owned_closure_body(
                *closure,
                &[Type::Any],
                None,
                Some(receiver),
                environment,
            ),
            Some(cfg::BlockOperand::Passed(value)) => values
                .get(value.0 as usize)
                .and_then(Option::as_ref)
                .and_then(optional_proc_type)
                .and_then(|block| proc_parts(&block).map(|(_, result)| result.clone()))
                .map_or_else(
                    || Some(Eval::value(Type::Any)),
                    |result| Some(Eval::value(result)),
                ),
            None => Some(Eval::value(Type::Any)),
        }
    }

    pub(super) fn cfg_owned_closure_type(
        &mut self,
        closure_id: hir::ClosureId,
        outer: &Environment,
    ) -> Option<Type> {
        let (body_id, parameters, span) = {
            let closure = self.program.hir_program.closure(closure_id)?;
            (closure.body, closure.parameters.clone(), closure.span)
        };
        let signature = Analyzer::inferred_hir_block_signature(&parameters);
        let mut closure_environment = outer.clone();
        let mut positional_index = 0;
        for parameter in &parameters.parameters {
            let type_ = match parameter.kind {
                hir::ParameterKind::Required
                | hir::ParameterKind::Optional
                | hir::ParameterKind::Post => {
                    let type_ = signature
                        .params
                        .get(positional_index)
                        .cloned()
                        .unwrap_or(Type::Any);
                    positional_index += 1;
                    type_
                }
                hir::ParameterKind::Rest | hir::ParameterKind::Forwarded => {
                    let type_ = signature
                        .params
                        .get(positional_index)
                        .cloned()
                        .unwrap_or(Type::Any);
                    positional_index += 1;
                    Type::Array(Box::new(type_))
                }
                hir::ParameterKind::RequiredKeyword | hir::ParameterKind::OptionalKeyword => {
                    Type::Any
                }
                hir::ParameterKind::KeywordRest => {
                    Type::Hash(Box::new(Type::Symbol), Box::new(Type::Any))
                }
                hir::ParameterKind::Block => Type::Proc(Vec::new(), Box::new(Type::Any)),
                hir::ParameterKind::Anonymous => Type::Any,
            };
            if let Some(name) = &parameter.name {
                closure_environment.bind(name.as_str().to_owned(), type_.clone());
            }
            if positional_index == 1 && parameter.name.is_none() {
                closure_environment.bind("it", type_);
            }
        }
        let body_result = self.eval_cfg_body_owned(
            SourceSite::from_span(span, None),
            body_id,
            &mut closure_environment,
            false,
        )?;
        Some(Type::Proc(signature.params, Box::new(body_result.type_)))
    }

    /// `define_method` accepts a block value as a method body.  The ordinary
    /// method table is intentionally not used for this shape: a passed block
    /// has no parser node to bind at this call site, and the body is checked
    /// through the enclosing caller's block contract instead.  Keep the
    /// language-level return contract here so owned CFG transfer does not
    /// fall back merely because the RBI cannot describe the dynamic binding.
    pub(super) fn cfg_passed_dynamic_method_type(
        &mut self,
        input: &OwnedCallInput,
        receiver_type: &Type,
        environment: &Environment,
    ) -> Option<Type> {
        let binding = match input.name.as_str() {
            "define_method" => BlockReceiverBinding::Instance,
            "define_singleton_method" => BlockReceiverBinding::Receiver,
            _ => return None,
        };
        if !matches!(input.block, Some(cfg::BlockOperand::Passed(_))) {
            return None;
        }
        if !matches!(
            input.receiver,
            cfg::ReceiverOperand::Implicit | cfg::ReceiverOperand::Value(_)
        ) {
            return None;
        }
        let receiver = match input.receiver {
            cfg::ReceiverOperand::Implicit => &environment.self_type,
            cfg::ReceiverOperand::Value(_) => receiver_type,
            cfg::ReceiverOperand::Super | cfg::ReceiverOperand::Yield => return None,
        };
        let receiver_is_declared_module = match receiver {
            Type::Named(name, _) => self
                .declarations
                .classes
                .get(name)
                .is_some_and(|info| info.is_module),
            _ => false,
        };
        if binding == BlockReceiverBinding::Instance
            && Self::class_object_instance_type(receiver).is_none()
            && !receiver.is_any()
            && !receiver_is_declared_module
        {
            return None;
        }
        if binding == BlockReceiverBinding::Receiver && receiver.is_never() {
            return None;
        }
        self.observe_cfg_define_method_binding(binding, environment);
        Some(Type::Symbol)
    }

    pub(super) fn observe_cfg_define_method_binding(
        &mut self,
        binding: BlockReceiverBinding,
        environment: &Environment,
    ) {
        let Some(current) = environment.method_key.as_ref() else {
            return;
        };
        let Some(state) = self.declarations.methods.get_mut(current) else {
            return;
        };
        if state.observe_block_receiver_binding(binding) {
            self.fixpoint.changed_methods.insert(current.clone());
        }
    }

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
        let block_receiver_binding = self
            .declarations
            .methods
            .get(&key)
            .and_then(|state| state.block_receiver_binding);
        let bound_receiver = class_new_receiver
            .or_else(|| match key.name.as_str() {
                "define_method" => Self::class_object_instance_type(receiver_type),
                "define_singleton_method" if !receiver_type.is_any() => Some(receiver_type.clone()),
                _ => None,
            })
            .or_else(|| self.active_support_test_block_receiver(&key, Some(receiver_type)))
            .or_else(|| {
                block_signature
                    .as_ref()
                    .and_then(optional_proc_type)
                    .and_then(|block| super::proc_receiver(&block).cloned())
            })
            .or_else(|| match block_receiver_binding {
                Some(BlockReceiverBinding::Instance) => {
                    Self::class_object_instance_type(receiver_type)
                }
                Some(BlockReceiverBinding::Receiver) => Some(receiver_type.clone()),
                Some(BlockReceiverBinding::Both) => {
                    let instance = Self::class_object_instance_type(receiver_type);
                    Some(instance.map_or_else(
                        || receiver_type.clone(),
                        |instance| Type::union([instance, receiver_type.clone()]),
                    ))
                }
                None => None,
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
            .program
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

    pub(super) fn transfer_owned_closure_body(
        &mut self,
        closure_id: hir::ClosureId,
        expected: &[Type],
        expected_return: Option<&Type>,
        bound_receiver: Option<&Type>,
        outer: &mut Environment,
    ) -> Option<Eval> {
        let closure = self.program.hir_program.closure(closure_id)?.clone();
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

        bind_owned_parameters(
            self,
            &closure.parameters,
            expected,
            &mut closure_environment,
        );
        let previous_expected_return = self.expected_return_type.take();
        self.expected_return_type = expected_return.map(|expected| {
            if matches!(expected, Type::TypeVar(_)) {
                owned_literal_block_tuple_type(&self.program.hir_program, closure_id)
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
    analyzer: &Analyzer<'_>,
    parameters: &hir::Parameters,
    expected: &[Type],
    environment: &mut Environment,
) {
    let required_parameters = parameters
        .parameters
        .iter()
        .filter(|parameter| parameter.kind == hir::ParameterKind::Required)
        .count();
    let destructured = if required_parameters > 1 {
        match expected {
            [Type::Tuple(elements)] => Some(elements.clone()),
            [Type::Array(_)] => {
                let element = analyzer.array_element_type(&expected[0]);
                match element {
                    Type::Tuple(elements) => Some(elements),
                    element => Some(vec![element; required_parameters]),
                }
            }
            _ => None,
        }
    } else {
        None
    };
    let expected = destructured.as_deref().unwrap_or(expected);
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
