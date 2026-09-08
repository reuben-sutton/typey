use super::{name_matches, Analyzer, CallArguments};
use crate::signature::MethodSig;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeSet;

impl<'src> Analyzer<'src> {
    pub(super) fn invoke_signature<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        block_return_type: Option<&Type>,
    ) -> Type {
        let mut type_parameter_bindings =
            self.infer_type_parameter_bindings(signature, arguments, block_return_type);
        type_parameter_bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            receiver_type,
        ));
        let keyword_mode = !signature.keywords.is_empty() || signature.accepts_keyword_rest;
        let argument_types = if keyword_mode {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        let mut dynamic_splat_shape_error = false;
        if arguments.has_dynamic_positional_splat {
            let expected_rest = signature
                .accepts_rest
                .then_some(signature.rest_index)
                .flatten()
                .filter(|index| *index == 0)
                .and_then(|_| signature.params.first())
                .map(|expected| {
                    self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    )
                });
            if let Some(expected) = expected_rest {
                for splat_type in &arguments.dynamic_positional_splat_types {
                    if let Some(element) = Self::dynamic_splat_element_type(splat_type) {
                        if !self.is_assignable(&element, &expected) {
                            self.check_assignable(node, &element, &expected);
                        }
                    } else {
                        dynamic_splat_shape_error = true;
                    }
                }
            } else {
                dynamic_splat_shape_error = true;
            }
            if dynamic_splat_shape_error {
                self.error(
                    node,
                    "Splats are only supported where the size of the array is known statically",
                );
            }
        }
        if arguments.has_dynamic_keyword_splat && !signature.accepts_keyword_rest {
            self.error(
                node,
                "Keyword args with splats are only supported where the shape of the hash is known statically",
            );
        }
        let positional_error = !arguments.forwards_arguments
            && !arguments.has_dynamic_positional_splat
            && !arguments.has_unknown_positional_splat
            && (argument_types.len() < signature.required_params
                || (!signature.accepts_rest && argument_types.len() > signature.params.len()));
        let provided_keywords = arguments
            .keyword_arguments
            .iter()
            .map(|argument| argument.name.as_str())
            .collect::<BTreeSet<_>>();
        let missing_keywords = !arguments.forwards_arguments
            && keyword_mode
            && !arguments.has_keyword_splat
            && signature.keywords.iter().any(|(name, parameter)| {
                parameter.required && !provided_keywords.contains(name.as_str())
            });
        let unknown_keyword = !arguments.forwards_arguments
            && keyword_mode
            && !signature.accepts_keyword_rest
            && arguments
                .keyword_arguments
                .iter()
                .any(|argument| !signature.keywords.contains_key(&argument.name));

        if self.checking_initializer {
            if argument_types.len() < signature.required_params {
                self.error(node, "Not enough arguments provided");
            } else if !signature.accepts_rest && argument_types.len() > signature.params.len() {
                self.error(node, "Too many arguments provided");
            }
            if missing_keywords {
                for (name, parameter) in &signature.keywords {
                    if parameter.required && !provided_keywords.contains(name.as_str()) {
                        self.error(node, format!("Missing required keyword argument `{name}`"));
                    }
                }
            }
            if self.initializer_requires_block
                && signature
                    .block
                    .as_ref()
                    .is_some_and(|block| matches!(block, Type::Proc(_, _) | Type::BoundProc { .. }))
                && !self.initializer_has_block
            {
                self.error(node, "`initialize` requires a block parameter");
            }
        } else if name == "new"
            && positional_error
            && argument_types.len() < signature.required_params
        {
            if let Some(owner) = receiver_type.and_then(Self::class_object_owner) {
                self.error(
                    node,
                    format!("Not enough arguments provided for method `{owner}.new`"),
                );
            } else {
                self.error(node, "Wrong number of arguments for `new`");
            }
        } else if positional_error || missing_keywords || unknown_keyword {
            let expected = if keyword_mode {
                let required_keywords = signature
                    .keywords
                    .iter()
                    .filter_map(|(name, parameter)| parameter.required.then_some(name.as_str()))
                    .collect::<Vec<_>>();
                if required_keywords.is_empty() {
                    signature.params.len().to_string()
                } else {
                    format!(
                        "at least {} positional arguments and keywords ({})",
                        signature.required_params,
                        required_keywords.join(", ")
                    )
                }
            } else if signature.required_params == signature.params.len() && !signature.accepts_rest
            {
                signature.params.len().to_string()
            } else {
                format!("at least {}", signature.required_params)
            };
            self.error(
                node,
                format!(
                    "Wrong number of arguments for `{name}`: expected {expected}, found {}",
                    argument_types.len() + arguments.keyword_arguments.len()
                ),
            );
        }
        if keyword_mode
            && !arguments.forwards_arguments
            && !arguments.has_unknown_positional_splat
            && !arguments.has_unknown_keyword_splat
        {
            for (index, (argument_index, actual)) in arguments
                .positional_indices
                .iter()
                .zip(argument_types)
                .enumerate()
            {
                if let (Some(argument), Some(expected)) = (
                    arguments.argument_nodes.get(*argument_index),
                    signature.positional_type(index, argument_types.len()),
                ) {
                    let expected = self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    self.check_assignable(argument, actual, &expected);
                }
            }
        } else if !arguments.forwards_arguments
            && !arguments.has_unknown_positional_splat
            && !arguments.has_unknown_keyword_splat
        {
            for (index, (argument_index, actual)) in arguments
                .argument_indices
                .iter()
                .zip(argument_types)
                .enumerate()
            {
                if arguments.has_dynamic_keyword_splat
                    && arguments
                        .argument_nodes
                        .get(*argument_index)
                        .is_some_and(|argument| argument.as_keyword_hash_node().is_some())
                {
                    continue;
                }
                if let (Some(argument), Some(expected)) = (
                    arguments.argument_nodes.get(*argument_index),
                    signature.positional_type(index, argument_types.len()),
                ) {
                    let expected = self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    self.check_assignable(argument, actual, &expected);
                }
            }
        }
        if keyword_mode && !arguments.forwards_arguments && !arguments.has_unknown_keyword_splat {
            for argument in &arguments.keyword_arguments {
                if let Some(expected) = signature.keywords.get(&argument.name) {
                    let expected = self.substitute_signature_type(
                        &expected.type_,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    self.check_assignable(&argument.node, &argument.type_, &expected);
                }
            }
        }
        if arguments.has_unknown_positional_splat || arguments.has_unknown_keyword_splat {
            Type::Any
        } else {
            let return_type = self.substitute_signature_type(
                &signature.return_type,
                receiver_type,
                &type_parameter_bindings,
                &signature.type_parameters,
            );
            if name == "flat_map" {
                if let Some(block_return_type) = block_return_type {
                    return Type::Array(Box::new(self.flat_map_element_type(block_return_type)));
                }
            }
            if matches!(name, "sort" | "sort_by") {
                if let Some(Type::Hash(key, value)) = receiver_type {
                    return Type::Array(Box::new(Type::Tuple(vec![
                        key.as_ref().clone(),
                        value.as_ref().clone(),
                    ])));
                }
            }
            if name == "to_h" {
                if let Some(block_return_type) = block_return_type {
                    if let Some((key, value)) = Self::pair_types(block_return_type) {
                        return Type::Hash(Box::new(key), Box::new(value));
                    }
                }
                if let Some(receiver_type) = receiver_type {
                    if let Some((key, value)) = Self::pair_types(receiver_type) {
                        return Type::Hash(Box::new(key), Box::new(value));
                    }
                }
            }
            if name == "grep" {
                if let Some(expected) = arguments
                    .argument_types
                    .first()
                    .and_then(Self::class_object_value_type)
                {
                    let element = match &return_type {
                        Type::Array(element) => Some(element.as_ref()),
                        Type::Named(class, arguments)
                            if arguments.len() == 1 && name_matches(class, "Array") =>
                        {
                            arguments.first()
                        }
                        _ => None,
                    };
                    if let Some(element) = element {
                        return Type::Array(Box::new(self.meet_predicate_type(element, &expected)));
                    }
                }
            }
            return_type
        }
    }
}
