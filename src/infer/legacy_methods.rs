//! Parser-backed method execution retained during the HIR migration.
//!
//! Method definitions and parameter binding still need Prism's parameter and
//! definition nodes while their owned HIR contracts are being completed. Keep
//! that compatibility boundary together instead of mixing it into the
//! analyzer coordinator.

use super::*;
use ruby_prism::{DefNode, Node, ParametersNode};

impl<'src> Analyzer<'src> {
    pub(super) fn eval_definition<'node>(
        &mut self,
        node: &Node<'node>,
        definition: &DefNode<'node>,
        outer: &mut Environment,
    ) -> Eval {
        let name = prism::constant_name(definition.name());
        let registered_key = self
            .declarations
            .definitions
            .get(&prism::span(node).0)
            .cloned()
            .unwrap_or_else(|| MethodKey::top_level(name.clone()));
        let key = if outer
            .method_key
            .as_ref()
            .is_some_and(|method| method.name == "<bound-block>")
        {
            Self::class_object_owner(&outer.self_type).map_or(registered_key.clone(), |owner| {
                MethodKey {
                    owner: Some(owner),
                    name: registered_key.name.clone(),
                    singleton: registered_key.singleton,
                }
            })
        } else {
            registered_key
        };
        if self.filter_method_bodies && !self.fixpoint.active_methods.contains(&key) {
            return Eval::value(Type::Nil);
        }
        self.begin_method_evaluation(&key);
        let previous_substitution_context = self.substitution_context.replace(key.clone());
        let state = self
            .declarations
            .methods
            .get(&key)
            .cloned()
            .unwrap_or_else(|| MethodState::inferred(definition.parameters()));
        if let Some(symbol) = definition
            .body()
            .and_then(|body| Self::trailing_symbol_literal(&body))
        {
            self.fixpoint
                .symbol_method_returns
                .insert(key.clone(), symbol);
        }
        let method_self_type = key.owner.as_ref().map_or(Type::Object, |owner| {
            if key.singleton {
                Self::class_object_type(owner)
            } else if self.is_concern_class_methods_module(owner) {
                // ActiveSupport::Concern copies a `ClassMethods` module into
                // the eventual including class. Its method bodies therefore
                // do not have the module object as `self`; the concrete host
                // is only known at the inclusion site.
                Type::Any
            } else {
                self.instance_self_type(owner)
            }
        });
        let mut method_environment = Environment {
            self_type: method_self_type,
            method_key: Some(key.clone()),
            ..Environment::default()
        };
        let body_signature = self.substitute_method_signature(
            &state.body_signature(),
            Some(&method_environment.self_type),
        );
        self.bind_parameters(
            definition.parameters(),
            Some(&body_signature),
            &mut method_environment,
            !state.explicit,
        );
        if !state.explicit {
            if let Some(shape) = self.declarations.parameter_shapes.get(&prism::span(node).0) {
                let mut positional_index = 0;
                for (name, kind) in &shape.parameter_kinds {
                    match kind {
                        signature::ParameterKind::Positional
                        | signature::ParameterKind::OptionalPositional
                        | signature::ParameterKind::RestPositional => {
                            if state
                                .params
                                .get(positional_index)
                                .is_some_and(Option::is_some)
                            {
                                method_environment.mark_inferred(name.clone());
                            } else {
                                method_environment.mark_provisional(name.clone());
                            }
                            positional_index += 1;
                        }
                        signature::ParameterKind::Keyword
                        | signature::ParameterKind::OptionalKeyword => {
                            if state.keywords.get(name).is_some_and(Option::is_some) {
                                method_environment.mark_inferred(name.clone());
                            } else {
                                method_environment.mark_provisional(name.clone());
                            }
                        }
                        signature::ParameterKind::RestKeyword | signature::ParameterKind::Block => {
                        }
                    }
                }
            }
        }
        if let Some(parameters) = definition.parameters() {
            if let Some(block) = parameters.block() {
                if let Some(name) = block.name() {
                    let block_type = body_signature.block.clone().unwrap_or_else(|| {
                        Type::Proc(
                            state.block_parameters(),
                            Box::new(state.block_result_type()),
                        )
                    });
                    // Keep the local binding consistent with `bind_parameters`:
                    // an omitted unannotated Ruby block is represented by nil.
                    let block_type = if !state.explicit {
                        Type::union([Type::Nil, block_type])
                    } else {
                        block_type
                    };
                    method_environment.bind(prism::constant_name(name), block_type);
                }
            }
        }

        let previous_expected_return = self.expected_return_type.take();
        self.expected_return_type = if state.explicit && !state.is_void {
            let signature = self.substitute_method_signature(
                &state.call_signature(),
                Some(&method_environment.self_type),
            );
            Some(signature.return_type)
        } else {
            None
        };
        let body_result = if let Some(body) = definition.body() {
            if self.config.enable_cfg {
                self.hir_body_ids
                    .get(&prism::span(node))
                    .copied()
                    .and_then(|body_id| {
                        self.eval_cfg_body_from_prism(&body, body_id, &mut method_environment, true)
                    })
                    .unwrap_or_else(|| self.eval_node(&body, &mut method_environment))
            } else {
                self.eval_node(&body, &mut method_environment)
            }
        } else {
            Eval::value(Type::Nil)
        };
        self.expected_return_type = previous_expected_return;
        let inferred_return = body_result.method_return_type();
        if self.fixpoint.collecting_returns {
            self.record_inferred_raise(key.clone(), body_result.abrupt.raise_type.clone());
        }
        if state.explicit && !state.is_void && !state.is_abstract && !self.is_rbi_definition(node) {
            let expected = self.substitute_method_signature(
                &state.call_signature(),
                Some(&method_environment.self_type),
            );
            let raw_signature = state.call_signature();
            let invalid_attached_class_context =
                (Self::contains_attached_class_type(&raw_signature.return_type)
                    || raw_signature
                        .params
                        .iter()
                        .any(Self::contains_attached_class_type))
                    && !self.attached_class_context_is_valid(&key);
            if !invalid_attached_class_context
                && !inferred_return.is_never()
                && !self.is_assignable(&inferred_return, &expected.return_type)
            {
                self.error(
                    node,
                    format!(
                        "Expected method `{name}` to return `{}`, but found `{}`",
                        expected.return_type, inferred_return
                    ),
                );
            }
        } else if self.fixpoint.collecting_returns {
            self.record_inferred_return(
                key,
                inferred_return,
                body_result.flow == Flow::abrupt(FlowKind::Raise),
            );
        }
        self.substitution_context = previous_substitution_context;
        let _ = outer;
        Eval::value(self.record(node, Type::Nil))
    }

    pub(super) fn trailing_symbol_literal<'node>(node: &Node<'node>) -> Option<String> {
        if let Some(statements) = node.as_statements_node() {
            return statements
                .body()
                .into_iter()
                .last()
                .and_then(|last| Self::trailing_symbol_literal(&last));
        }
        node.as_symbol_node()
            .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
    }

    pub(super) fn eval_super<'node>(
        &mut self,
        node: &Node<'node>,
        hir_call: Option<&hir::Call>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        forwarding: Option<&ruby_prism::ForwardingSuperNode<'node>>,
        block: Option<&Node<'node>>,
        environment: &mut Environment,
    ) -> Type {
        let Some(current) = environment.method_key.clone() else {
            return Type::Any;
        };
        let target = self.super_method_key(&current);
        let arguments = if forwarding.is_some() {
            let types = self
                .declarations
                .methods
                .get(&current)
                .map(|state| state.call_signature().params)
                .unwrap_or_default();
            let positional_types = types.clone();
            CallArguments {
                argument_nodes: Vec::new(),
                argument_sites: Vec::new(),
                argument_types: types,
                argument_indices: Vec::new(),
                positional_indices: Vec::new(),
                positional_types,
                keyword_arguments: Vec::new(),
                keyword_hash_indices: Vec::new(),
                has_keyword_splat: false,
                has_dynamic_positional_splat: false,
                dynamic_positional_splat_types: Vec::new(),
                has_dynamic_keyword_splat: false,
                has_unknown_positional_splat: false,
                has_unknown_keyword_splat: false,
                forwards_arguments: true,
            }
        } else {
            let argument_inputs = if let Some(call) = hir_call {
                hir_call_argument_inputs(&call.arguments, arguments)
            } else {
                prism_call_argument_inputs(arguments)
            };
            self.evaluate_call_arguments(argument_inputs, environment)
                .arguments
        };
        let Some(target) = target else {
            if let Some(block) = block {
                let _ = self.eval_block_node(block, &[Type::Any], environment);
            }
            return Type::Any;
        };
        self.record_method_dependency(&target, environment);
        let Some(signature) = self.observe_call(&target, &arguments, block.is_some()) else {
            if let Some(block) = block {
                let _ = self.eval_block_node(block, &[Type::Any], environment);
            }
            return Type::Any;
        };
        let receiver_type = environment.self_type.clone();
        let block_return_type = self.observe_block_call(
            &target,
            block,
            &signature,
            &arguments,
            Some(&receiver_type),
            environment,
        );
        self.invoke_signature(
            node,
            &target.name,
            &signature,
            &arguments,
            Some(&environment.self_type),
            block_return_type.as_ref(),
        )
    }

    pub(super) fn bind_parameters<'node>(
        &mut self,
        parameters: Option<ParametersNode<'node>>,
        signature: Option<&MethodSig>,
        environment: &mut Environment,
        block_optional: bool,
    ) {
        let Some(parameters) = parameters else { return };
        let inferred_context = environment
            .method_key
            .as_ref()
            .and_then(|key| self.declarations.methods.get(key))
            .is_some_and(|state| !state.explicit);
        let mut index = 0;
        for parameter in &parameters.requireds() {
            let type_ = signature
                .and_then(|signature| signature.params.get(index))
                .cloned()
                .unwrap_or(Type::Any);
            if parameter.as_multi_target_node().is_some() {
                self.bind_for_target(&parameter, type_, environment);
            } else if let Some(required) = parameter.as_required_parameter_node() {
                self.bind_parameter(environment, required.name(), signature, index);
            }
            index += 1;
        }
        for parameter in &parameters.optionals() {
            if let Some(optional) = parameter.as_optional_parameter_node() {
                self.bind_parameter(environment, optional.name(), signature, index);
                let previous_expected_return = self.expected_return_type.take();
                self.expected_return_type = signature
                    .and_then(|signature| signature.params.get(index))
                    .cloned();
                let mut default_environment = environment.clone();
                self.eval_node(&optional.value(), &mut default_environment);
                self.expected_return_type = previous_expected_return;
                *environment = environment.join(&default_environment);
                index += 1;
            }
        }
        if let Some(rest) = parameters
            .rest()
            .and_then(|node| node.as_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                let element_type = signature
                    .and_then(|signature| signature.params.get(index))
                    .cloned()
                    .unwrap_or(Type::Any);
                environment.bind(
                    prism::constant_name(name),
                    Type::Array(Box::new(element_type)),
                );
            }
            index += 1;
        }
        for parameter in &parameters.posts() {
            if let Some(post) = parameter.as_required_parameter_node() {
                self.bind_parameter(environment, post.name(), signature, index);
                index += 1;
            }
        }
        for parameter in &parameters.keywords() {
            if let Some(required) = parameter.as_required_keyword_parameter_node() {
                self.bind_keyword_parameter(environment, required.name(), signature);
            } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                self.bind_keyword_parameter(environment, optional.name(), signature);
                let previous_expected_return = self.expected_return_type.take();
                self.expected_return_type = signature
                    .and_then(|signature| {
                        signature
                            .keywords
                            .get(&prism::constant_name(optional.name()))
                    })
                    .map(|parameter| parameter.type_.clone());
                self.eval_node(&optional.value(), environment);
                self.expected_return_type = previous_expected_return;
            }
        }
        if let Some(rest) = parameters
            .keyword_rest()
            .and_then(|node| node.as_keyword_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                environment.bind(
                    prism::constant_name(name),
                    Type::Hash(Box::new(Type::Symbol), Box::new(Type::Any)),
                );
            }
        }
        if let Some(block) = parameters.block() {
            if let Some(name) = block.name() {
                let type_ = signature
                    .and_then(|signature| signature.block.clone())
                    .unwrap_or_else(|| Type::Proc(Vec::new(), Box::new(Type::Any)));
                // A Ruby `&block` local is nil when the caller did not pass a
                // block, even when the method's callable block signature is
                // known. The call-site signature still describes the block
                // accepted by the method; this local needs the runtime
                // nilability so `if block`/`unless block` can refine it.
                let type_ = if block_optional {
                    Type::union([Type::Nil, type_])
                } else {
                    type_
                };
                environment.bind(prism::constant_name(name), type_);
            }
        }
        if inferred_context {
            for parameter in &parameters.requireds() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            for parameter in &parameters.optionals() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            if let Some(rest) = parameters.rest() {
                self.mark_inferred_parameter(&rest, environment);
            }
            for parameter in &parameters.posts() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            for parameter in &parameters.keywords() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            if let Some(rest) = parameters.keyword_rest() {
                self.mark_inferred_parameter(&rest, environment);
            }
            if let Some(block) = parameters.block() {
                if let Some(name) = block.name() {
                    environment.mark_inferred(prism::constant_name(name));
                }
            }
        }
    }

    fn mark_inferred_parameter<'node>(
        &self,
        parameter: &Node<'node>,
        environment: &mut Environment,
    ) {
        if let Some(required) = parameter.as_required_parameter_node() {
            environment.mark_inferred(prism::constant_name(required.name()));
        } else if let Some(optional) = parameter.as_optional_parameter_node() {
            environment.mark_inferred(prism::constant_name(optional.name()));
        } else if let Some(rest) = parameter.as_rest_parameter_node() {
            if let Some(name) = rest.name() {
                environment.mark_inferred(prism::constant_name(name));
            }
        } else if let Some(keyword) = parameter.as_required_keyword_parameter_node() {
            environment.mark_inferred(prism::constant_name(keyword.name()));
        } else if let Some(keyword) = parameter.as_optional_keyword_parameter_node() {
            environment.mark_inferred(prism::constant_name(keyword.name()));
        } else if let Some(rest) = parameter.as_keyword_rest_parameter_node() {
            if let Some(name) = rest.name() {
                environment.mark_inferred(prism::constant_name(name));
            }
        } else if let Some(block) = parameter.as_block_parameter_node() {
            if let Some(name) = block.name() {
                environment.mark_inferred(prism::constant_name(name));
            }
        } else if let Some(multi) = parameter.as_multi_target_node() {
            for target in &multi.lefts() {
                self.mark_inferred_parameter(&target, environment);
            }
            if let Some(rest) = multi.rest() {
                self.mark_inferred_parameter(&rest, environment);
            }
            for target in &multi.rights() {
                self.mark_inferred_parameter(&target, environment);
            }
        }
    }

    fn bind_parameter<'node>(
        &self,
        environment: &mut Environment,
        name: ruby_prism::ConstantId<'node>,
        signature: Option<&MethodSig>,
        index: usize,
    ) {
        let type_ = signature
            .and_then(|signature| signature.params.get(index))
            .cloned()
            .unwrap_or(Type::Any);
        let parameter_name = prism::constant_name(name);
        environment.bind(parameter_name, type_);
    }

    fn bind_keyword_parameter<'node>(
        &self,
        environment: &mut Environment,
        name: ruby_prism::ConstantId<'node>,
        signature: Option<&MethodSig>,
    ) {
        let name = prism::constant_name(name);
        let type_ = signature
            .and_then(|signature| signature.keywords.get(&name))
            .map_or(Type::Any, |parameter| parameter.type_.clone());
        environment.bind(name, type_);
    }
}
