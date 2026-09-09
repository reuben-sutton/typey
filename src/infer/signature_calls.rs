use super::{name_matches, Analyzer, CallArguments, MethodKey, SourceSite};
use crate::prism;
use crate::signature::MethodSig;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
enum SignatureDiagnosticSite<'a, 'node> {
    Node(&'a Node<'node>),
    Source(SourceSite),
}

impl<'src> Analyzer<'src> {
    pub(super) fn observe_call(
        &mut self,
        key: &MethodKey,
        arguments: &CallArguments<'_>,
        has_block: bool,
    ) -> Option<MethodSig> {
        let key = self.resolve_method_key(key)?;
        if let Some(state) = self
            .declarations
            .methods
            .get(&key)
            .filter(|state| state.explicit)
        {
            let fallback = state.call_signature();
            let overloads = if state.overloads.is_empty() {
                vec![fallback.clone()]
            } else {
                state.overloads.clone()
            };
            return Some(
                self.select_overload(&overloads, arguments, has_block)
                    .unwrap_or(fallback),
            );
        }
        let (signature, changed) = {
            let recursive_inferred = self
                .substitution_context
                .as_ref()
                .and_then(|current| self.resolve_method_key(current))
                .is_some_and(|current| {
                    current == key
                        && self
                            .declarations
                            .methods
                            .get(&current)
                            .is_some_and(|state| !state.explicit)
                });
            let state = self.declarations.methods.get_mut(&key)?;
            let mut changed = false;
            let positional_types: &[Type] =
                if state.accepts_keyword_rest || !state.keywords.is_empty() {
                    &arguments.positional_types
                } else {
                    &arguments.argument_types
                };
            // A direct recursive call often passes a value derived from the
            // current method parameter. Observing that provisional `Any`
            // argument would permanently poison the parameter summary before
            // an external call can provide concrete evidence.
            let recursive_arguments_concrete = !positional_types.iter().any(Type::contains_any)
                && arguments
                    .keyword_arguments
                    .iter()
                    .all(|argument| !argument.type_.contains_any());
            let partial_forwarding =
                arguments.forwarded_positional_start.is_some() || arguments.forwards_keywords;
            if (!recursive_inferred || recursive_arguments_concrete)
                && (!arguments.forwards_arguments || partial_forwarding)
                && !arguments.has_unknown_positional_splat
                && !arguments.has_unknown_keyword_splat
            {
                let observed_positional_types = arguments
                    .forwarded_positional_start
                    .map_or(positional_types, |start| {
                        positional_types.get(..start).unwrap_or_default()
                    });
                changed |= state.observe_arguments(observed_positional_types);
                if state.accepts_keyword_rest || !state.keywords.is_empty() {
                    for argument in &arguments.keyword_arguments {
                        changed |= state.observe_keyword(&argument.name, &argument.type_);
                    }
                }
            }
            (state.call_signature(), changed)
        };
        if changed {
            self.fixpoint.changed_methods.insert(key);
        }
        Some(signature)
    }

    fn select_overload(
        &self,
        overloads: &[MethodSig],
        arguments: &CallArguments<'_>,
        has_block: bool,
    ) -> Option<MethodSig> {
        let matching = overloads
            .iter()
            .enumerate()
            .filter(|(_, signature)| self.signature_accepts_arguments(signature, arguments))
            .collect::<Vec<_>>();
        let block_preference = |signature: &MethodSig| {
            if has_block == signature.block.is_some() {
                0
            } else {
                1
            }
        };
        matching
            .into_iter()
            .min_by_key(|(index, signature)| {
                let positional_count =
                    if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
                        arguments.positional_types.len()
                    } else {
                        arguments.argument_types.len()
                    };
                (
                    block_preference(signature),
                    signature.params.len().saturating_sub(positional_count),
                    *index,
                )
            })
            .map(|(_, signature)| signature.clone())
    }

    fn signature_accepts_arguments(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
    ) -> bool {
        if !self.signature_shape_accepts_arguments(signature, arguments) {
            return false;
        }
        if arguments.forwards_arguments
            || arguments.has_dynamic_positional_splat
            || arguments.has_dynamic_keyword_splat
            || arguments.has_unknown_positional_splat
            || arguments.has_unknown_keyword_splat
        {
            return true;
        }
        let keyword_mode = !signature.keywords.is_empty() || signature.accepts_keyword_rest;
        let positional_types = if keyword_mode {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        let type_parameter_bindings =
            self.infer_type_parameter_bindings(signature, arguments, None);
        if !positional_types.iter().enumerate().all(|(index, actual)| {
            let Some(expected) = signature.positional_type(index, positional_types.len()) else {
                return false;
            };
            let expected = self.substitute_signature_type(
                expected,
                None,
                &type_parameter_bindings,
                &signature.type_parameters,
            );
            self.is_assignable(actual, &expected) || matches!(expected, Type::TypeVar(_))
        }) {
            return false;
        }
        if keyword_mode
            && !arguments.has_keyword_splat
            && !arguments.keyword_arguments.iter().all(|argument| {
                signature
                    .keywords
                    .get(&argument.name)
                    .is_some_and(|expected| {
                        let expected = self.substitute_signature_type(
                            &expected.type_,
                            None,
                            &type_parameter_bindings,
                            &signature.type_parameters,
                        );
                        self.is_assignable(&argument.type_, &expected)
                            || matches!(expected, Type::TypeVar(_))
                    })
                    || signature.accepts_keyword_rest
            })
        {
            return false;
        }
        true
    }

    fn signature_shape_accepts_arguments(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
    ) -> bool {
        if arguments.forwards_arguments
            || arguments.has_dynamic_positional_splat
            || arguments.has_dynamic_keyword_splat
            || arguments.has_unknown_positional_splat
            || arguments.has_unknown_keyword_splat
        {
            return true;
        }
        let keyword_mode = !signature.keywords.is_empty() || signature.accepts_keyword_rest;
        let positional_types = if keyword_mode {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        if positional_types.len() < signature.required_params
            || (!signature.accepts_rest && positional_types.len() > signature.params.len())
        {
            return false;
        }
        if keyword_mode && !arguments.has_keyword_splat {
            let provided = arguments
                .keyword_arguments
                .iter()
                .map(|argument| argument.name.as_str())
                .collect::<BTreeSet<_>>();
            if signature
                .keywords
                .iter()
                .any(|(name, parameter)| parameter.required && !provided.contains(name.as_str()))
            {
                return false;
            }
            if !signature.accepts_keyword_rest
                && arguments
                    .keyword_arguments
                    .iter()
                    .any(|argument| !signature.keywords.contains_key(&argument.name))
            {
                return false;
            }
        }
        true
    }

    pub(super) fn invoke_signature<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        block_return_type: Option<&Type>,
    ) -> Type {
        self.invoke_signature_at_site(
            SignatureDiagnosticSite::Node(node),
            name,
            signature,
            arguments,
            receiver_type,
            block_return_type,
        )
    }

    pub(super) fn invoke_signature_at(
        &mut self,
        site: SourceSite,
        name: &str,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
        receiver_type: Option<&Type>,
        block_return_type: Option<&Type>,
    ) -> Type {
        self.invoke_signature_at_site(
            SignatureDiagnosticSite::Source(site),
            name,
            signature,
            arguments,
            receiver_type,
            block_return_type,
        )
    }

    fn signature_error(
        &mut self,
        site: SignatureDiagnosticSite<'_, '_>,
        message: impl Into<String>,
    ) {
        match site {
            SignatureDiagnosticSite::Node(node) => self.error(node, message),
            SignatureDiagnosticSite::Source(site) => self.error_at(site, message),
        }
    }

    fn signature_check_assignable(
        &mut self,
        site: SignatureDiagnosticSite<'_, '_>,
        actual: &Type,
        expected: &Type,
    ) {
        match site {
            SignatureDiagnosticSite::Node(node) => self.check_assignable(node, actual, expected),
            SignatureDiagnosticSite::Source(site) => {
                self.check_assignable_at(site, actual, expected)
            }
        }
    }

    fn invoke_signature_at_site<'node>(
        &mut self,
        diagnostic_site: SignatureDiagnosticSite<'_, 'node>,
        name: &str,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        block_return_type: Option<&Type>,
    ) -> Type {
        let source_site = match diagnostic_site {
            SignatureDiagnosticSite::Node(node) => SourceSite::from_prism_span(prism::span(node)),
            SignatureDiagnosticSite::Source(site) => site,
        };
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
                .filter(|index| *index <= argument_types.len())
                .and_then(|index| signature.params.get(index))
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
                            self.signature_check_assignable(diagnostic_site, &element, &expected);
                        }
                    } else {
                        dynamic_splat_shape_error = true;
                    }
                }
            } else {
                dynamic_splat_shape_error = true;
            }
            if dynamic_splat_shape_error {
                self.signature_error(
                    diagnostic_site,
                    "Splats are only supported where the size of the array is known statically",
                );
            }
        }
        if arguments.has_dynamic_keyword_splat && !signature.accepts_keyword_rest {
            self.signature_error(
                diagnostic_site,
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
                self.signature_error(diagnostic_site, "Not enough arguments provided");
            } else if !signature.accepts_rest && argument_types.len() > signature.params.len() {
                self.signature_error(diagnostic_site, "Too many arguments provided");
            }
            if missing_keywords {
                for (name, parameter) in &signature.keywords {
                    if parameter.required && !provided_keywords.contains(name.as_str()) {
                        self.signature_error(
                            diagnostic_site,
                            format!("Missing required keyword argument `{name}`"),
                        );
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
                self.signature_error(diagnostic_site, "`initialize` requires a block parameter");
            }
        } else if name == "new"
            && positional_error
            && argument_types.len() < signature.required_params
        {
            if let Some(owner) = receiver_type.and_then(Self::class_object_owner) {
                self.signature_error(
                    diagnostic_site,
                    format!("Not enough arguments provided for method `{owner}.new`"),
                );
            } else {
                self.signature_error(diagnostic_site, "Wrong number of arguments for `new`");
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
            self.signature_error(
                diagnostic_site,
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
                if let Some(expected) = signature.positional_type(index, argument_types.len()) {
                    let expected = self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    let site = arguments
                        .argument_nodes
                        .get(*argument_index)
                        .map(|node| SignatureDiagnosticSite::Node(node))
                        .unwrap_or_else(|| {
                            SignatureDiagnosticSite::Source(
                                arguments
                                    .argument_sites
                                    .get(*argument_index)
                                    .copied()
                                    .unwrap_or(source_site),
                            )
                        });
                    self.signature_check_assignable(site, actual, &expected);
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
                    && arguments.keyword_hash_indices.contains(argument_index)
                {
                    continue;
                }
                if let Some(expected) = signature.positional_type(index, argument_types.len()) {
                    let expected = self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    let site = arguments
                        .argument_nodes
                        .get(*argument_index)
                        .map(|node| SignatureDiagnosticSite::Node(node))
                        .unwrap_or_else(|| {
                            SignatureDiagnosticSite::Source(
                                arguments
                                    .argument_sites
                                    .get(*argument_index)
                                    .copied()
                                    .unwrap_or(source_site),
                            )
                        });
                    self.signature_check_assignable(site, actual, &expected);
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
                    let site = argument
                        .node
                        .as_ref()
                        .map(SignatureDiagnosticSite::Node)
                        .unwrap_or(SignatureDiagnosticSite::Source(argument.site));
                    self.signature_check_assignable(site, &argument.type_, &expected);
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
