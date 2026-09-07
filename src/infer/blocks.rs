use super::{
    name_matches, optional_proc_type, prism, proc_parts, strictness_rank, Analyzer, CallArguments,
    CallSite, Environment, Eval, MethodKey, MethodState, Strictness,
};
use crate::signature::MethodSig;
use crate::types::Type;
use ruby_prism::{Node, ParametersNode};

impl<'src> Analyzer<'src> {
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
        let Some(block) = node.as_block_node() else {
            return (Type::Any, outer.clone());
        };
        let captured = outer.clone();
        let (result, block_environment) = self.eval_block_with_environment(&block, expected, outer);
        self.propagate_block_locals(outer, &captured, &block_environment);
        (Self::block_value_type(&result), block_environment)
    }

    pub(super) fn eval_bound_block_node<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        receiver: &Type,
        outer: &mut Environment,
    ) -> Type {
        let Some(block) = node.as_block_node() else {
            return Type::Any;
        };
        let captured = outer.clone();
        let mut bound_outer = outer.clone();
        bound_outer.self_type = receiver.clone();
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
        Self::block_value_type(&result)
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
        let Some((parameters, result)) = proc_parts(type_) else {
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
                    format!("Integer({})", prism::text(self.source, &value))
                } else {
                    prism::text(self.source, &value)
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
}
