use super::{
    name_matches, optional_proc_type, prism, proc_parts, proc_receiver, strictness_rank, Analyzer,
    BlockReceiverBinding, CallArguments, CallSite, Environment, Eval, KeywordArgument, MethodKey,
    MethodState, SourceSite, Strictness,
};
use crate::hir;
use crate::signature::{self, MethodSig};
use crate::types::Type;
use ruby_prism::{Node, ParametersNode};

impl<'src> Analyzer<'src> {
    /// `define_method` binds its block to instances of the receiver's class.
    /// Preserve that runtime fact when an inferred helper such as a test DSL
    /// forwards `&block`; otherwise a class-level declaration block is checked
    /// with the declaring class object as `self` instead of the eventual
    /// instance.
    pub(super) fn observe_define_method_binding(
        &mut self,
        name: &str,
        arguments: &CallArguments<'_>,
        block: Option<&Node<'_>>,
        environment: &Environment,
    ) {
        let binding = match name {
            "define_method" => BlockReceiverBinding::Instance,
            "define_singleton_method" => BlockReceiverBinding::Receiver,
            _ => return,
        };
        if block.is_none()
            && !arguments
                .argument_nodes
                .iter()
                .any(|argument| argument.as_block_argument_node().is_some())
        {
            return;
        }
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

    pub(super) fn eval_block_node<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        outer: &mut Environment,
    ) -> Type {
        self.eval_block_node_with_environment(node, expected, outer)
            .0
    }

    pub(super) fn eval_block_node_with_environment<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        outer: &mut Environment,
    ) -> (Type, Environment) {
        let (result, block_environment) =
            self.eval_block_node_result_with_environment(node, expected, outer);
        (Self::block_value_type(&result), block_environment)
    }

    pub(super) fn eval_block_node_result_with_environment<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        outer: &mut Environment,
    ) -> (Eval, Environment) {
        let Some(block) = node.as_block_node() else {
            return (Eval::value(Type::Any), outer.clone());
        };
        let captured = outer.clone();
        let (result, block_environment) = self.eval_block_with_environment(&block, expected, outer);
        self.propagate_block_locals(outer, &captured, &block_environment);
        (result, block_environment)
    }

    pub(super) fn eval_bound_block_node<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        receiver: &Type,
        outer: &mut Environment,
    ) -> Type {
        Self::block_value_type(
            &self
                .eval_bound_block_node_result(node, expected, receiver, outer)
                .0,
        )
    }

    pub(super) fn eval_bound_block_node_result<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        receiver: &Type,
        outer: &mut Environment,
    ) -> (Eval, Environment) {
        let Some(block) = node.as_block_node() else {
            return (Eval::value(Type::Any), outer.clone());
        };
        let captured = outer.clone();
        let mut bound_outer = outer.clone();
        bound_outer.self_type = match receiver {
            Type::AttachedClassOf(owner) => Type::named(owner.clone()),
            _ => receiver.clone(),
        };
        let class_object_owner = Self::class_object_owner(receiver);
        bound_outer.method_key = Some(MethodKey {
            owner: class_object_owner
                .clone()
                .or_else(|| Self::named_type_name(receiver))
                .or_else(|| outer.method_key.as_ref().and_then(|key| key.owner.clone())),
            name: "<bound-block>".to_owned(),
            singleton: class_object_owner.is_some(),
        });
        let (result, block_environment) =
            self.eval_block_with_environment(&block, expected, &bound_outer);
        self.propagate_block_locals(outer, &captured, &block_environment);
        (result, block_environment)
    }

    pub(super) fn passed_block_expression_type<'node>(
        &mut self,
        node: &Node<'node>,
        outer: &mut Environment,
    ) -> Option<Type> {
        let block = node.as_block_argument_node()?;
        let expression = block.expression()?;
        let type_ = self.eval_node(&expression, outer).type_;
        (!type_.is_nil()).then_some(type_)
    }

    pub(super) fn passed_block_signature(type_: &Type) -> Option<Type> {
        match type_ {
            // `bind_parameters` uses an empty `Proc` with an untyped result
            // for an unannotated or `Proc`-typed block parameter.  That is an
            // unknown-arity proc, not a known zero-argument proc.
            Type::Proc(parameters, result) if parameters.is_empty() && result.is_any() => None,
            Type::Proc(_, _) | Type::BoundProc { .. } => Some(type_.clone()),
            Type::Union(_) => {
                optional_proc_type(type_).and_then(|proc| Self::passed_block_signature(&proc))
            }
            _ => None,
        }
    }

    pub(super) fn block_type_description(type_: &Type) -> String {
        let type_ = Self::unresolved_block_type_as_anything(type_);
        let Some((parameters, result)) = proc_parts(&type_) else {
            return type_.to_string();
        };
        let mut description = String::from("T.proc");
        if !parameters.is_empty() {
            description.push_str(".params(");
            for (index, parameter) in parameters.iter().enumerate() {
                if index > 0 {
                    description.push_str(", ");
                }
                description.push_str(&format!("arg{index}: {parameter}"));
            }
            description.push(')');
        }
        description.push_str(&format!(".returns({result})"));
        description
    }

    fn unresolved_block_type_as_anything(type_: &Type) -> Type {
        match type_ {
            Type::TypeVar(_) => Type::Anything,
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(Self::unresolved_block_type_as_anything)
                    .collect(),
            ),
            Type::Array(element) => {
                Type::Array(Box::new(Self::unresolved_block_type_as_anything(element)))
            }
            Type::Hash(key, value) => Type::Hash(
                Box::new(Self::unresolved_block_type_as_anything(key)),
                Box::new(Self::unresolved_block_type_as_anything(value)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(Self::unresolved_block_type_as_anything)
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(Self::unresolved_block_type_as_anything)
                    .collect(),
                Box::new(Self::unresolved_block_type_as_anything(result)),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(Self::unresolved_block_type_as_anything(receiver)),
                parameters: parameters
                    .iter()
                    .map(Self::unresolved_block_type_as_anything)
                    .collect(),
                result: Box::new(Self::unresolved_block_type_as_anything(result)),
            },
            Type::Union(members) => {
                Type::union(members.iter().map(Self::unresolved_block_type_as_anything))
            }
            Type::Intersection(members) => {
                Type::intersection(members.iter().map(Self::unresolved_block_type_as_anything))
            }
            other => other.clone(),
        }
    }

    pub(super) fn sorbet_type_description(type_: &Type) -> String {
        match type_ {
            Type::Named(name, arguments) if name_matches(name, "Class") && arguments.len() == 1 => {
                format!("T.class_of({})", arguments[0])
            }
            _ => type_.to_string(),
        }
    }

    pub(super) fn argument_type_description(&self, node: &Node<'_>, type_: &Type) -> String {
        let Some(hash) = node.as_keyword_hash_node() else {
            return type_.to_string();
        };
        let fields = hash
            .elements()
            .into_iter()
            .filter_map(|element| {
                let assoc = element.as_assoc_node()?;
                let key = assoc.key().as_symbol_node()?;
                let value = assoc.value();
                let name = String::from_utf8_lossy(key.unescaped());
                let value = if value.as_integer_node().is_some() {
                    format!("Integer({})", prism::text(self.program.source, &value))
                } else {
                    prism::text(self.program.source, &value)
                };
                Some(format!("{name}: {value}"))
            })
            .collect::<Vec<_>>();
        if fields.is_empty() {
            type_.to_string()
        } else {
            format!("{{{}}}", fields.join(", "))
        }
    }

    pub(super) fn eval_collection_block<'node>(
        &mut self,
        node: &Node<'node>,
        element: &Type,
        outer: &mut Environment,
    ) -> Type {
        let previous_expected_return = self.expected_return_type.take();
        let literal_tuple = node
            .as_block_node()
            .and_then(|block| block.body())
            .and_then(|body| {
                body.as_array_node().or_else(|| {
                    body.as_statements_node().and_then(|statements| {
                        statements
                            .body()
                            .into_iter()
                            .last()
                            .and_then(|last| last.as_array_node())
                    })
                })
            })
            .and_then(|array| {
                array
                    .elements()
                    .iter()
                    .all(|element| element.as_splat_node().is_none())
                    .then(|| Type::Tuple(vec![Type::Any; array.elements().len()]))
            });
        self.expected_return_type = previous_expected_return
            .as_ref()
            .and_then(|expected| match expected {
                Type::Array(element) => Some((**element).clone()),
                Type::Named(name, arguments)
                    if arguments.len() == 1 && name_matches(name, "Enumerable") =>
                {
                    Some(arguments[0].clone())
                }
                _ => None,
            })
            .or(literal_tuple);

        let result = if let Some(block) = node.as_block_argument_node() {
            if let Some(symbol) = block
                .expression()
                .and_then(|expression| expression.as_symbol_node())
            {
                let name = String::from_utf8_lossy(symbol.unescaped()).into_owned();
                self.eval_symbol_collection_block(node, element, &name, outer)
            } else {
                let Some(expression_type) = self.passed_block_expression_type(node, outer) else {
                    return Type::Any;
                };
                let Some(signature) = Self::passed_block_signature(&expression_type) else {
                    if strictness_rank(self.strictness_at(prism::span(node).0))
                        >= strictness_rank(Strictness::Strict)
                    {
                        let expected = Type::Proc(vec![element.clone()], Box::new(Type::Anything));
                        self.error(
                            node,
                            format!(
                                "Cannot use a `Proc` with unknown arity as a `{}`",
                                Self::block_type_description(&expected)
                            ),
                        );
                    }
                    return Type::Any;
                };
                let Some((_, result)) = proc_parts(&signature) else {
                    return Type::Any;
                };
                let expected = Type::Proc(vec![element.clone()], Box::new(Type::Anything));
                if !self.is_assignable(&signature, &expected) {
                    self.error(
                        node,
                        format!(
                            "Expected `{}` but found `{}` for block argument",
                            Self::block_type_description(&expected),
                            Self::block_type_description(&signature),
                        ),
                    );
                }
                result.clone()
            }
        } else {
            self.eval_block_node(node, std::slice::from_ref(element), outer)
        };
        self.expected_return_type = previous_expected_return;
        result
    }

    pub(super) fn literal_block_tuple_type(node: &Node<'_>) -> Option<Type> {
        let array = node
            .as_block_node()
            .and_then(|block| block.body())
            .and_then(|body| {
                body.as_array_node().or_else(|| {
                    body.as_statements_node().and_then(|statements| {
                        statements
                            .body()
                            .into_iter()
                            .last()
                            .and_then(|last| last.as_array_node())
                    })
                })
            })?;
        array
            .elements()
            .iter()
            .all(|element| element.as_splat_node().is_none())
            .then(|| Type::Tuple(vec![Type::Any; array.elements().len()]))
    }

    pub(super) fn eval_symbol_collection_block<'node>(
        &mut self,
        node: &Node<'node>,
        receiver: &Type,
        name: &str,
        environment: &mut Environment,
    ) -> Type {
        self.eval_symbol_collection_block_inner(node, receiver, name, environment, None)
    }

    pub(super) fn eval_symbol_collection_block_inner<'node>(
        &mut self,
        node: &Node<'node>,
        receiver: &Type,
        name: &str,
        environment: &mut Environment,
        union_context: Option<&Type>,
    ) -> Type {
        if let Type::Union(members) = receiver {
            return members.iter().fold(Type::Never, |result, member| {
                result.join(&self.eval_symbol_collection_block_inner(
                    node,
                    member,
                    name,
                    environment,
                    Some(receiver),
                ))
            });
        }

        let arguments = CallArguments::default();
        let mut resolved = false;
        let type_ = if let Some(key) = self.receiver_method_key(None, receiver, name, environment) {
            self.record_method_dependency(&key, environment);
            if let Some(signature) = self.observe_call(&key, &arguments, false) {
                resolved = true;
                self.invoke_signature(node, name, &signature, &arguments, Some(receiver), None)
            } else {
                let site = CallSite {
                    argument_nodes: &arguments.argument_nodes,
                    argument_types: &arguments.argument_types,
                    block: None,
                };
                self.eval_method_call(receiver, name, &site, environment)
            }
        } else {
            let site = CallSite {
                argument_nodes: &arguments.argument_nodes,
                argument_types: &arguments.argument_types,
                block: None,
            };
            self.eval_method_call(receiver, name, &site, environment)
        };
        if type_.is_any() && !receiver.contains_any() && !receiver.is_never() && !resolved {
            let component =
                union_context.map_or_else(String::new, |union| format!(" component of `{union}`"));
            self.error(
                node,
                format!("Method `{name}` does not exist on `{receiver}`{component}"),
            );
        }
        type_
    }

    pub(super) fn inferred_block_signature<'node>(node: &Node<'node>) -> MethodSig {
        let parameters = node
            .as_block_node()
            .and_then(|block| block.parameters())
            .and_then(|parameters| {
                parameters
                    .as_block_parameters_node()
                    .and_then(|parameters| parameters.parameters())
                    .or_else(|| parameters.as_parameters_node())
            });
        MethodState::inferred(parameters).body_signature()
    }

    pub(super) fn inferred_hir_block_signature(parameters: &hir::Parameters) -> MethodSig {
        MethodState::inferred_hir(parameters).body_signature()
    }

    pub(super) fn block_value_type(result: &Eval) -> Type {
        let type_ = result
            .normal_type
            .clone()
            .unwrap_or(Type::Never)
            .join(&result.abrupt.next_type);
        if type_.is_never() {
            Type::Any
        } else {
            type_
        }
    }

    pub(super) fn eval_block<'node>(
        &mut self,
        block: &ruby_prism::BlockNode<'node>,
        expected: &[Type],
        outer: &mut Environment,
    ) -> Eval {
        let captured = outer.clone();
        let (result, environment) = self.eval_block_with_environment(block, expected, outer);
        self.propagate_block_locals(outer, &captured, &environment);
        result
    }

    pub(super) fn eval_block_with_environment<'node>(
        &mut self,
        block: &ruby_prism::BlockNode<'node>,
        expected: &[Type],
        outer: &Environment,
    ) -> (Eval, Environment) {
        let mut environment = outer.clone();
        if let Some(parameters) = block.parameters() {
            if let Some(parameters) = parameters
                .as_block_parameters_node()
                .and_then(|parameters| parameters.parameters())
            {
                let expected = Self::destructure_block_parameters(&parameters, expected);
                self.bind_parameters(
                    Some(parameters),
                    Some(&MethodSig::new(expected, Type::Any)),
                    &mut environment,
                    true,
                );
            } else if let Some(parameters) = parameters.as_parameters_node() {
                let expected = Self::destructure_block_parameters(&parameters, expected);
                self.bind_parameters(
                    Some(parameters),
                    Some(&MethodSig::new(expected, Type::Any)),
                    &mut environment,
                    true,
                );
            } else if parameters.as_it_parameters_node().is_some()
                || parameters.as_numbered_parameters_node().is_some()
            {
                for (index, type_) in expected.iter().enumerate() {
                    environment.bind(format!("_{}", index + 1), type_.clone());
                }
                if let Some(type_) = expected.first() {
                    environment.bind("it", type_.clone());
                }
            }
        } else {
            for (index, type_) in expected.iter().enumerate() {
                environment.bind(format!("_{}", index + 1), type_.clone());
            }
            if let Some(type_) = expected.first() {
                environment.bind("it", type_.clone());
            }
        }
        let result = if let Some(body) = block.body() {
            self.eval_node(&body, &mut environment)
        } else {
            Eval::value(Type::Nil)
        };
        (result, environment)
    }

    pub(super) fn block_parameter_name<'node>(node: &Node<'node>, index: usize) -> Option<String> {
        let block = node.as_block_node()?;
        let parameters = block.parameters()?;
        let parameters = parameters
            .as_block_parameters_node()
            .and_then(|parameters| parameters.parameters())
            .or_else(|| parameters.as_parameters_node())?;
        parameters
            .requireds()
            .into_iter()
            .filter_map(|parameter| parameter.as_required_parameter_node())
            .nth(index)
            .map(|parameter| prism::constant_name(parameter.name()))
    }

    pub(super) fn block_has_multiple_required_parameters(node: &Node<'_>) -> bool {
        let Some(block) = node.as_block_node() else {
            return false;
        };
        let Some(parameters) = block.parameters() else {
            return false;
        };
        let parameters = parameters
            .as_block_parameters_node()
            .and_then(|parameters| parameters.parameters())
            .or_else(|| parameters.as_parameters_node());
        parameters.is_some_and(|parameters| parameters.requireds().len() > 1)
    }

    pub(super) fn destructure_block_parameters<'node>(
        parameters: &ParametersNode<'node>,
        expected: &[Type],
    ) -> Vec<Type> {
        if parameters.requireds().len() > 1 {
            if let [Type::Tuple(elements)] = expected {
                return elements.clone();
            }
        }
        expected.to_vec()
    }

    pub(super) fn propagate_block_locals(
        &self,
        outer: &mut Environment,
        captured: &Environment,
        block: &Environment,
    ) {
        for name in captured.locals.keys() {
            let type_ = captured.get(name).join(&block.get(name));
            outer.bind(name.clone(), type_);
        }
    }

    pub(super) fn observe_block_call_eval<'node>(
        &mut self,
        key: &MethodKey,
        block: Option<&Node<'node>>,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        environment: &mut Environment,
    ) -> Option<Eval> {
        let Some(block) = block else {
            return None;
        };
        let Some(key) = self.resolve_method_key(key) else {
            return None;
        };
        let mut bindings = self.infer_type_parameter_bindings(signature, arguments, None);
        bindings.extend(self.infer_generic_member_bindings(signature, arguments, receiver_type));
        let previous_substitution_context = self.substitution_context.replace(key.clone());
        let block_signature = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                receiver_type,
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
        let previous_expected_return = self.expected_return_type.take();
        let expected_block_return = block_signature
            .as_ref()
            .and_then(optional_proc_type)
            .and_then(|block| proc_parts(&block).map(|(_, result)| result.clone()));
        self.expected_return_type = expected_block_return.map(|expected| {
            if matches!(expected, Type::TypeVar(_)) {
                Self::literal_block_tuple_type(block).unwrap_or(expected)
            } else {
                expected
            }
        });
        let class_new_receiver = (key.name == "new"
            && key.singleton
            && key
                .owner
                .as_deref()
                .is_some_and(|owner| name_matches(owner, "Class")))
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
            .or_else(|| self.active_support_test_block_receiver(&key, receiver_type))
            .or_else(|| {
                block_signature
                    .as_ref()
                    .and_then(optional_proc_type)
                    .and_then(|block| proc_receiver(&block).cloned())
            })
            .or_else(|| match block_receiver_binding {
                Some(BlockReceiverBinding::Instance) => {
                    receiver_type.and_then(Self::class_object_instance_type)
                }
                Some(BlockReceiverBinding::Receiver) => receiver_type.cloned(),
                Some(BlockReceiverBinding::Both) => receiver_type.map(|receiver| {
                    let instance = Self::class_object_instance_type(receiver);
                    instance.map_or_else(
                        || receiver.clone(),
                        |instance| Type::union([instance, receiver.clone()]),
                    )
                }),
                None => None,
            })
            .or_else(|| self.rails_initializer_block_receiver(&key, receiver_type))
            .or_else(|| self.rails_application_configure_block_receiver(&key, receiver_type))
            .or_else(|| self.rails_route_draw_block_receiver(&key, receiver_type))
            .or_else(|| self.active_support_ci_block_receiver(&key, receiver_type));
        let (block_result, passed_block_signature) = if block.as_block_argument_node().is_some() {
            if let Some(expected_signature) = block_signature.as_ref().and_then(optional_proc_type)
            {
                if block
                    .as_block_argument_node()
                    .and_then(|block| block.expression())
                    .and_then(|expression| expression.as_symbol_node())
                    .is_some()
                {
                    (
                        Eval::value(self.eval_symbol_passed_block(
                            block,
                            &expected_signature,
                            environment,
                        )),
                        None,
                    )
                } else {
                    let Some(expression_type) =
                        self.passed_block_expression_type(block, environment)
                    else {
                        // `&nil` is Ruby's spelling for omitting a block.
                        return None;
                    };
                    if let Some(signature) = Self::passed_block_signature(&expression_type) {
                        let return_type =
                            proc_parts(&signature).map_or(Type::Any, |(_, result)| result.clone());
                        (Eval::value(return_type), Some(signature))
                    } else {
                        (Eval::value(Type::Any), None)
                    }
                }
            } else {
                let Some(expression_type) = self.passed_block_expression_type(block, environment)
                else {
                    // `&nil` is Ruby's spelling for omitting a block.
                    return None;
                };
                if let Some(signature) = Self::passed_block_signature(&expression_type) {
                    let return_type =
                        proc_parts(&signature).map_or(Type::Any, |(_, result)| result.clone());
                    (Eval::value(return_type), Some(signature))
                } else {
                    (Eval::value(Type::Any), None)
                }
            }
        } else if matches!(
            key.name.as_str(),
            "define_method" | "define_singleton_method"
        ) {
            // These APIs consume the block as a method body rather than as a
            // callback.  Their core RBI supplies a generic block signature,
            // so handle the body here before the ordinary callback path can
            // accidentally retain the lexical module/class self.
            self.eval_dynamic_method_body(&key.name, block, environment);
            (Eval::value(Type::Any), None)
        } else {
            let block_result = if let Some(receiver) = bound_receiver.as_ref() {
                self.eval_bound_block_node_result(block, &expected, receiver, environment)
                    .0
            } else {
                self.eval_block_node_result_with_environment(block, &expected, environment)
                    .0
            };
            (block_result, None)
        };
        let block_type = Self::block_value_type(&block_result);
        self.expected_return_type = previous_expected_return;
        let mut checked_bindings =
            self.infer_type_parameter_bindings(signature, arguments, Some(&block_type));
        checked_bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            receiver_type,
        ));
        let checked_block_signature = self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| state.explicit)
            .then(|| {
                let previous_substitution_context = self.substitution_context.replace(key.clone());
                let result = signature.block.as_ref().map(|block| {
                    self.substitute_signature_type(
                        block,
                        receiver_type,
                        &checked_bindings,
                        &signature.type_parameters,
                    )
                });
                self.substitution_context = previous_substitution_context;
                result
            })
            .flatten();
        if let Some(actual_block_signature) = passed_block_signature {
            // A passed block is checked against the contract before its
            // return value is used to infer the caller's type parameter. If
            // we use `checked_bindings` here, `Array#map`'s result parameter
            // is already bound to the block's return type and the diagnostic
            // incorrectly presents that inferred type as the expected
            // contract.
            if let Some(expected_block_signature) =
                block_signature.as_ref().and_then(optional_proc_type)
            {
                let expected_for_check =
                    Self::unresolved_block_type_as_anything(&expected_block_signature);
                if !Self::passed_block_is_assignable(
                    self,
                    &actual_block_signature,
                    &expected_for_check,
                ) {
                    self.error(
                        block,
                        format!(
                            "Expected `{}` but found `{}` for block argument",
                            Self::block_type_description(&expected_block_signature),
                            Self::block_type_description(&actual_block_signature),
                        ),
                    );
                }
            }
        } else if let Some(block_signature) = checked_block_signature
            .as_ref()
            .and_then(optional_proc_type)
        {
            if let Some((_, expected_return)) = proc_parts(&block_signature) {
                if !expected_return.is_any()
                    && !expected_return.is_nil()
                    && !self.is_assignable(&block_type, &expected_return)
                {
                    self.check_assignable(block, &block_type, &expected_return);
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

    pub(super) fn observe_block_call<'node>(
        &mut self,
        key: &MethodKey,
        block: Option<&Node<'node>>,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        environment: &mut Environment,
    ) -> Option<Type> {
        self.observe_block_call_eval(key, block, signature, arguments, receiver_type, environment)
            .map(|result| Self::block_value_type(&result))
    }

    pub(super) fn eval_symbol_passed_block<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &Type,
        environment: &mut Environment,
    ) -> Type {
        let Some(symbol) = node
            .as_block_argument_node()
            .and_then(|block| block.expression())
            .and_then(|expression| expression.as_symbol_node())
        else {
            return Type::Any;
        };
        let name = String::from_utf8_lossy(symbol.unescaped()).into_owned();
        self.eval_symbol_passed_block_named(
            Some(node),
            SourceSite::from_prism_span(prism::span(node)),
            &name,
            expected,
            environment,
        )
    }

    pub(super) fn eval_symbol_passed_block_named(
        &mut self,
        node: Option<&Node<'_>>,
        site: SourceSite,
        name: &str,
        expected: &Type,
        environment: &mut Environment,
    ) -> Type {
        let Some((parameters, _)) = proc_parts(expected) else {
            return Type::Any;
        };
        let Some(receiver) = parameters.first() else {
            return Type::Any;
        };
        self.eval_symbol_passed_block_for_receiver(
            node,
            site,
            name,
            parameters,
            receiver,
            environment,
            None,
        )
    }

    fn eval_symbol_passed_block_for_receiver(
        &mut self,
        node: Option<&Node<'_>>,
        site: SourceSite,
        name: &str,
        parameters: &[Type],
        receiver: &Type,
        environment: &mut Environment,
        union_context: Option<&Type>,
    ) -> Type {
        if let Type::Union(members) = receiver {
            return members.iter().fold(Type::Never, |result, member| {
                result.join(&self.eval_symbol_passed_block_for_receiver(
                    node,
                    site,
                    name,
                    parameters,
                    member,
                    environment,
                    Some(receiver).or(union_context),
                ))
            });
        }

        let Some(key) = self.receiver_method_key(None, receiver, &name, environment) else {
            return self.eval_symbol_passed_block_fallback(
                node,
                site,
                name,
                receiver,
                union_context,
                &CallArguments::default(),
                environment,
            );
        };
        self.record_method_dependency(&key, environment);
        let Some(initial_signature) = self.observe_call(&key, &CallArguments::default(), false)
        else {
            return self.eval_symbol_passed_block_fallback(
                node,
                site,
                name,
                receiver,
                union_context,
                &CallArguments::default(),
                environment,
            );
        };
        // Symbol#to_proc consumes the first yielded value as the receiver;
        // all remaining yielded values are passed to the named method.
        let arguments = Self::symbol_method_arguments(parameters, &initial_signature, site);
        let signature = self
            .observe_call(&key, &arguments, false)
            .unwrap_or(initial_signature);
        let owner = self
            .resolve_method_key(&key)
            .and_then(|resolved| resolved.owner)
            .unwrap_or_else(|| receiver.to_string());
        let method = format!("{owner}#{name}");
        let positional = &arguments.positional_types;
        if !signature.accepts_rest && positional.len() > signature.params.len() {
            self.error_at_or_node(
                node,
                site,
                format!(
                    "Too many positional arguments provided for method `{method}`. Expected: `{}`, got: `{}`",
                    signature.params.len(),
                    positional.len(),
                ),
            );
        }
        for (index, actual) in positional.iter().enumerate() {
            if let Some(expected) = signature.positional_type(index, positional.len()) {
                if !self.is_assignable(actual, expected) {
                    self.error_at_or_node(
                        node,
                        site,
                        format!(
                            "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                        ),
                    );
                }
            }
        }
        for (name, parameter) in &signature.keywords {
            let Some(argument) = arguments
                .keyword_arguments
                .iter()
                .find(|argument| argument.name == *name)
            else {
                if parameter.required {
                    self.error_at_or_node(
                        node,
                        site,
                        format!("Missing required keyword argument `{name}` for method `{method}`"),
                    );
                }
                continue;
            };
            if !self.is_assignable(&argument.type_, &parameter.type_) {
                self.error_at_or_node(
                    node,
                    site,
                    format!(
                        "Expected `{}` but found `{}` for argument `{name}`",
                        parameter.type_, argument.type_
                    ),
                );
            }
        }
        self.substitute_signature_type(
            &signature.return_type,
            Some(receiver),
            &std::collections::BTreeMap::new(),
            &signature.type_parameters,
        )
    }

    fn symbol_method_arguments(
        parameters: &[Type],
        signature: &MethodSig,
        site: SourceSite,
    ) -> CallArguments<'static> {
        let mut arguments = CallArguments::default();
        for parameter in parameters.iter().skip(1) {
            let mut keyword = false;
            if let Type::Named(shape, _) = parameter {
                for name in signature.keywords.keys() {
                    if let Some(type_) = signature::parse_inline_record_field(shape, name) {
                        arguments.keyword_arguments.push(KeywordArgument {
                            name: name.clone(),
                            node: None,
                            site,
                            type_,
                        });
                        keyword = true;
                    }
                }
            }
            if !keyword {
                arguments.argument_types.push(parameter.clone());
                arguments.positional_types.push(parameter.clone());
            }
        }
        arguments.argument_indices = (0..arguments.argument_types.len()).collect();
        arguments.positional_indices = (0..arguments.positional_types.len()).collect();
        arguments
    }

    fn passed_block_is_assignable(analyzer: &Analyzer<'_>, actual: &Type, expected: &Type) -> bool {
        let Some((expected_parameters, expected_return)) = proc_parts(expected) else {
            return analyzer.is_assignable(actual, expected);
        };
        let Some((_, actual_return)) = proc_parts(actual) else {
            return false;
        };
        if expected_parameters.is_empty() {
            // A block contract such as `T.proc.returns(String)` does not
            // constrain the block's arity. This is also how an inferred
            // method's unannotated `&block` is represented.
            analyzer.is_assignable(actual_return, expected_return)
        } else {
            analyzer.is_assignable(actual, expected)
        }
    }

    fn eval_symbol_passed_block_fallback(
        &mut self,
        node: Option<&Node<'_>>,
        site: SourceSite,
        name: &str,
        receiver: &Type,
        union_context: Option<&Type>,
        arguments: &CallArguments<'_>,
        environment: &mut Environment,
    ) -> Type {
        let call_site = CallSite {
            argument_nodes: &arguments.argument_nodes,
            argument_types: &arguments.argument_types,
            block: None,
        };
        let type_ = self.eval_method_call(receiver, name, &call_site, environment);
        if type_.is_any() && !receiver.contains_any() && !receiver.is_never() {
            let component =
                union_context.map_or_else(String::new, |union| format!(" component of `{union}`"));
            self.error_at_or_node(
                node,
                site,
                format!("Method `{name}` does not exist on `{receiver}`{component}"),
            );
        }
        type_
    }
}
