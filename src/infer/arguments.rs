use super::{
    Analyzer, CallArgumentEvaluation, CallArguments, Environment, Eval, Flow, FlowKind,
    KeywordArgument, OutcomeTypes,
};
use crate::types::Type;
use ruby_prism::Node;

impl<'src> Analyzer<'src> {
    pub(super) fn evaluate_call_arguments<'node>(
        &mut self,
        argument_nodes: Vec<Node<'node>>,
        environment: &mut Environment,
    ) -> CallArgumentEvaluation<'node> {
        let mut evaluated = CallArguments::default();
        let mut abrupt = OutcomeTypes::default();
        let mut abrupt_flow = Flow::empty();
        let mut all_normal = true;

        for (argument_index, argument) in argument_nodes.iter().enumerate() {
            if argument.as_forwarding_arguments_node().is_some() {
                evaluated.forwards_arguments = true;
                continue;
            }
            if let Some(keyword_hash) = argument.as_keyword_hash_node() {
                let mut key = Type::Never;
                let mut value = Type::Never;
                let mut keyword_arguments = Vec::new();
                let mut keyword_shape = true;
                let mut child_flow = Flow::normal();
                let mut child_abrupt = OutcomeTypes::default();

                for child in &keyword_hash.elements() {
                    if let Some(assoc) = child.as_assoc_node() {
                        let key_node = assoc.key();
                        let key_result = self.eval_node(&key_node, environment);
                        key = key.join(&key_result.type_);
                        child_abrupt = child_abrupt.join(&key_result.abrupt);
                        child_flow = child_flow.without(FlowKind::Normal).union(key_result.flow);

                        let value_node = assoc.value();
                        let value_result = self.eval_node(&value_node, environment);
                        value = value.join(&value_result.type_);
                        child_abrupt = child_abrupt.join(&value_result.abrupt);
                        child_flow = child_flow
                            .without(FlowKind::Normal)
                            .union(value_result.flow);

                        if let Some(symbol) = key_node.as_symbol_node() {
                            keyword_arguments.push(KeywordArgument {
                                name: String::from_utf8_lossy(symbol.unescaped()).into_owned(),
                                node: value_node,
                                type_: value_result.type_,
                            });
                        } else {
                            keyword_shape = false;
                        }
                    } else if let Some(splat) = child.as_assoc_splat_node() {
                        if let Some(expression) = splat.value() {
                            let result = self.eval_node(&expression, environment);
                            child_abrupt = child_abrupt.join(&result.abrupt);
                            child_flow = child_flow.without(FlowKind::Normal).union(result.flow);
                            let result_type = result.type_.clone();
                            if let Type::Hash(splat_key, splat_value) = result_type {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                                evaluated.has_dynamic_keyword_splat = true;
                            } else {
                                key = Type::Any;
                                value = Type::Any;
                                if result_type.is_any() {
                                    evaluated.has_unknown_keyword_splat = true;
                                } else {
                                    evaluated.has_dynamic_keyword_splat = true;
                                }
                            }
                        }
                        evaluated.has_keyword_splat = true;
                    } else {
                        keyword_shape = false;
                        let result = self.eval_node(&child, environment);
                        child_abrupt = child_abrupt.join(&result.abrupt);
                        child_flow = child_flow.without(FlowKind::Normal).union(result.flow);
                    }
                }

                if keyword_shape {
                    let key = if key.is_never() { Type::Any } else { key };
                    let value = if value.is_never() { Type::Any } else { value };
                    let type_ = self.apply_inline_assertion(
                        argument,
                        Type::Hash(Box::new(key), Box::new(value)),
                    );
                    let type_ = self.record(argument, type_);
                    evaluated.argument_types.push(type_);
                    evaluated.argument_indices.push(argument_index);
                    evaluated.keyword_arguments.extend(keyword_arguments);
                    abrupt = abrupt.join(&child_abrupt);
                    abrupt_flow = abrupt_flow.union(child_flow.without(FlowKind::Normal));
                    all_normal &= child_flow.contains(FlowKind::Normal);
                    continue;
                }
            }

            if let Some(splat) = argument.as_splat_node() {
                let Some(expression) = splat.expression() else {
                    evaluated.forwards_arguments = true;
                    continue;
                };
                let result = self.eval_splat_expression(&expression, environment);
                if let Type::Tuple(elements) = &result.type_ {
                    for type_ in elements {
                        evaluated.argument_types.push(type_.clone());
                        evaluated.argument_indices.push(argument_index);
                        evaluated.positional_types.push(type_.clone());
                        evaluated.positional_indices.push(argument_index);
                    }
                } else if result.type_.is_any() {
                    evaluated.has_unknown_positional_splat = true;
                } else {
                    evaluated.has_dynamic_positional_splat = true;
                    evaluated
                        .dynamic_positional_splat_types
                        .push(result.type_.clone());
                }
                abrupt = abrupt.join(&result.abrupt);
                abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
                all_normal &= result.flow.contains(FlowKind::Normal);
                continue;
            }

            let result = self.eval_node(argument, environment);
            evaluated.argument_types.push(result.type_.clone());
            evaluated.argument_indices.push(argument_index);
            evaluated.positional_types.push(result.type_);
            evaluated.positional_indices.push(argument_index);
            abrupt = abrupt.join(&result.abrupt);
            abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
            all_normal &= result.flow.contains(FlowKind::Normal);
        }

        // Keyword hashes remain in the complete argument list for built-in
        // method models, but only their named entries participate in a
        // keyword-shaped signature.
        evaluated.argument_nodes = argument_nodes;
        CallArgumentEvaluation {
            arguments: evaluated,
            abrupt,
            abrupt_flow,
            all_normal,
        }
    }

    pub(super) fn eval_splat_expression<'node>(
        &mut self,
        expression: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let previous_expected_return = self.expected_return_type.take();
        if let Some(array) = expression.as_array_node() {
            if array
                .elements()
                .iter()
                .all(|element| element.as_splat_node().is_none())
            {
                self.expected_return_type =
                    Some(Type::Tuple(vec![Type::Any; array.elements().len()]));
            }
        }
        let result = self.eval_node(expression, environment);
        self.expected_return_type = previous_expected_return;
        result
    }
}
