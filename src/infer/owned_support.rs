//! Small shared contracts used by owned HIR/CFG transfer.
//!
//! These helpers used to live beside the recursive evaluator. Keeping them in
//! a parser-free support module makes their ownership explicit: they are
//! lattice and declaration operations, not a second Ruby execution path.

use super::*;

impl<'src> Analyzer<'src> {
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

    pub(super) fn inferred_hir_block_signature(parameters: &hir::Parameters) -> MethodSig {
        MethodState::inferred_hir(parameters).body_signature()
    }

    pub(super) fn passed_block_signature(type_: &Type) -> Option<Type> {
        match type_ {
            // An empty Proc with an untyped result represents unknown arity,
            // not a known zero-argument callback.
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

    pub(super) fn passed_block_is_assignable(
        analyzer: &Analyzer<'_>,
        actual: &Type,
        expected: &Type,
    ) -> bool {
        let Some((expected_parameters, expected_return)) = proc_parts(expected) else {
            return analyzer.is_assignable(actual, expected);
        };
        let Some((actual_parameters, actual_return)) = proc_parts(actual) else {
            return false;
        };
        let symbolic_return = Self::is_forwarded_block_return(actual_return);
        // Sorbet's `void` block contract permits a callback to return a value;
        // the value is discarded by the caller.  Its parameter contract still
        // applies, so check contravariance without imposing `NilClass` on the
        // callback result.
        if matches!(expected_return, Type::Nil) {
            return symbolic_return
                || (actual_parameters.len() == expected_parameters.len()
                    && actual_parameters
                        .iter()
                        .zip(expected_parameters)
                        .all(|(actual, expected)| analyzer.is_assignable(expected, actual)));
        }
        if expected_parameters.is_empty() {
            symbolic_return || analyzer.is_assignable(actual_return, expected_return)
        } else {
            symbolic_return || analyzer.is_assignable(actual, expected)
        }
    }

    fn is_forwarded_block_return(type_: &Type) -> bool {
        matches!(type_, Type::TypeVar(name) if name.starts_with("$block_return:"))
    }

    pub(super) fn eval_owned_symbol_passed_block_named(
        &mut self,
        site: SourceSite,
        name: &str,
        expected: &Type,
        environment: &mut Environment,
    ) -> Option<Type> {
        let Some((parameters, _)) = proc_parts(expected) else {
            return Some(Type::Any);
        };
        let Some(receiver) = parameters.first() else {
            return Some(Type::Any);
        };
        let initial_signature = self
            .receiver_method_key(None, receiver, name, environment)
            .and_then(|key| {
                self.record_method_dependency(&key, environment);
                self.observe_call(&key, &CallArguments::default(), false)
            });
        let arguments = Self::symbol_method_arguments(parameters, initial_signature.as_ref(), site);
        let receiver_operand = cfg::ReceiverOperand::Implicit;
        let call_name = hir::Name::new(name);
        let call_arguments = Vec::new();
        let input = OwnedCallInput::new(
            site,
            None,
            &receiver_operand,
            &call_name,
            &call_arguments,
            None,
            false,
            false,
        );
        self.transfer_owned_symbol_call(&input, receiver, &arguments, environment)
            .ok()
    }

    fn symbol_method_arguments(
        parameters: &[Type],
        signature: Option<&MethodSig>,
        site: SourceSite,
    ) -> CallArguments<'static> {
        let mut arguments = CallArguments::default();
        for parameter in parameters.iter().skip(1) {
            let mut keyword = false;
            if let Type::Named(shape, _) = parameter {
                if let Some(signature) = signature {
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

    pub(super) fn forwarded_block_signature(
        &mut self,
        local_name: &str,
        actual: &Type,
        expected_parameters: &[Type],
        environment: &mut Environment,
    ) -> Option<Type> {
        if !environment.is_block_parameter(local_name) {
            return None;
        }
        let actual_proc = optional_proc_type(actual)?;
        if expected_parameters.is_empty()
            || proc_parts(&actual_proc).is_some_and(|(parameters, _)| !parameters.is_empty())
        {
            return None;
        }
        let key = environment.method_key.clone()?;
        let state = self.declarations.methods.get_mut(&key)?;
        if state.explicit {
            return None;
        }
        let variable = Type::TypeVar(format!(
            "$block_return:{}:{}:{}",
            key.owner.as_deref().unwrap_or("<top>"),
            key.name,
            key.singleton
        ));
        let signature = Type::Proc(expected_parameters.to_vec(), Box::new(variable.clone()));
        let local_type = if actual.is_nil() {
            Type::Nil
        } else {
            Type::union([Type::Nil, signature.clone()])
        };
        environment.bind_block_parameter(local_name.to_owned(), local_type);
        let mut changed = state.observe_yield_arguments(expected_parameters);
        changed |= state.observe_block_return(&variable);
        if changed {
            self.fixpoint.changed_methods.insert(key);
        }
        Some(signature)
    }

    pub(super) fn propagate_block_locals(
        &self,
        outer: &mut Environment,
        captured: &Environment,
        block: &Environment,
    ) {
        for name in captured.locals.keys() {
            outer.bind(name.clone(), captured.get(name).join(&block.get(name)));
        }
    }

    pub(super) fn multi_assignment_element_type(
        &self,
        type_: &Type,
        index: usize,
        known_length: Option<usize>,
    ) -> Type {
        match type_ {
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.multi_assignment_element_type(member, index, known_length)),
            ),
            Type::Tuple(elements) => elements.get(index).cloned().unwrap_or(Type::Nil),
            Type::Array(element) => {
                if known_length.is_some_and(|length| index >= length) {
                    Type::Nil
                } else if known_length.is_some() {
                    element.as_ref().clone()
                } else {
                    Type::union([element.as_ref().clone(), Type::Nil])
                }
            }
            Type::Nil => Type::Nil,
            Type::Any => Type::Any,
            _ => Type::Any,
        }
    }

    pub(super) fn definitely_comparable_array_element(&self, left: &Type, right: &Type) -> bool {
        match (left, right) {
            (Type::Integer, Type::Integer)
            | (Type::Integer, Type::Float)
            | (Type::Float, Type::Integer)
            | (Type::Float, Type::Float)
            | (Type::String, Type::String)
            | (Type::Symbol, Type::Symbol) => true,
            (left, Type::Array(right)) => self.definitely_comparable_array_element(left, right),
            (left, Type::Tuple(right)) => right
                .iter()
                .all(|right| self.definitely_comparable_array_element(left, right)),
            (Type::Union(left), right) => left
                .iter()
                .all(|left| self.definitely_comparable_array_element(left, right)),
            (left, Type::Union(right)) => right
                .iter()
                .all(|right| self.definitely_comparable_array_element(left, right)),
            _ => false,
        }
    }

    pub(super) fn tuple_literal_argument_type<'node>(
        &self,
        node: &Node<'node>,
        actual: &Type,
        expected: &Type,
    ) -> Type {
        let Type::Tuple(expected_elements) = expected else {
            return actual.clone();
        };
        let Some(array) = node.as_array_node() else {
            return actual.clone();
        };
        let elements = array.elements();
        if elements.len() != expected_elements.len()
            || elements
                .iter()
                .any(|element| element.as_splat_node().is_some())
        {
            return actual.clone();
        }
        let mut inferred = Vec::with_capacity(elements.len());
        for element in &elements {
            let span = prism::span(&element);
            let Some(type_) = self
                .reporting
                .types
                .iter()
                .rev()
                .find(|inferred| inferred.start == span.0 && inferred.end == span.1)
                .map(|inferred| inferred.type_.clone())
            else {
                return actual.clone();
            };
            inferred.push(type_);
        }
        Type::Tuple(inferred)
    }

    pub(super) fn global_call_type(&self, name: &str, argument_types: &[Type]) -> Option<Type> {
        match name {
            "puts" | "print" | "p" | "pp" | "warn" | "loop" => Some(Type::Nil),
            "is_a?" | "kind_of?" | "instance_of?" | "respond_to?" | "frozen?" | "block_given?" => {
                Some(Type::bool())
            }
            "Array" => Some(argument_types.first().map_or_else(
                || Type::Array(Box::new(Type::Any)),
                |type_| Type::Array(Box::new(self.array_coercion_element_type(type_))),
            )),
            "Hash" => Some(Type::Hash(Box::new(Type::Any), Box::new(Type::Any))),
            "Integer" => Some(Type::Integer),
            "Float" => Some(Type::Float),
            "String" => Some(Type::String),
            "Symbol" => Some(Type::Symbol),
            "__dir__" => Some(Type::String),
            "__method__" | "__callee__" => Some(Type::Symbol),
            "gem" => Some(Type::named("Gem::Specification")),
            "require" | "require_relative" | "load" => Some(Type::bool()),
            "to_enum" | "enum_for" => Some(Type::named("Enumerator")),
            "binding" => Some(Type::named("Binding")),
            "singleton_class" => Some(Type::Named("Class".to_owned(), vec![Type::Anything])),
            "rand" => Some(Type::Float),
            "sleep" | "id" | "object_id" | "hash" => Some(Type::Integer),
            "const_get" => Some(Type::Object),
            "raise" | "fail" | "abort" | "exit" | "exit!" | "throw" => Some(Type::Never),
            "sig" => Some(Type::Nil),
            "private_class_method"
            | "has_attached_class!"
            | "type_member"
            | "type_template"
            | "mixes_in_class_methods"
            | "each"
            | "alias_method"
            | "attr_reader"
            | "attr_writer"
            | "attr_accessor"
            | "private"
            | "protected"
            | "public"
            | "module_function"
            | "autoload"
            | "private_constant"
            | "public_constant"
            | "refine" => Some(Type::Nil),
            _ => None,
        }
    }

    pub(super) fn widen_overridable_noreturn(
        &self,
        key: &MethodKey,
        mut signature: MethodSig,
    ) -> MethodSig {
        let Some(resolved) = self.resolve_method_key(key) else {
            return signature;
        };
        let Some(state) = self.declarations.methods.get(&resolved) else {
            return signature;
        };
        if !state.explicit && state.return_type.is_none() {
            signature.return_type = Type::Any;
            return signature;
        }
        if state.explicit
            || !state.return_terminates
            || !state.return_type.as_ref().is_some_and(Type::is_never)
        {
            return signature;
        }
        let Some(owner) = resolved.owner.as_deref() else {
            return signature;
        };
        let mut override_type = Type::Never;
        let mut found_override = false;
        for (candidate, candidate_state) in &self.declarations.methods {
            if candidate.singleton != resolved.singleton
                || candidate.name != resolved.name
                || candidate.owner.as_deref() == Some(owner)
            {
                continue;
            }
            let Some(candidate_owner) = candidate.owner.as_deref() else {
                continue;
            };
            if !self.nominal_subtype_names(nominal_name(candidate_owner), nominal_name(owner)) {
                continue;
            }
            found_override = true;
            let Some(return_type) = candidate_state.return_type.as_ref() else {
                signature.return_type = Type::union([Type::Nil, Type::Object]);
                return signature;
            };
            if return_type.is_any() {
                signature.return_type = Type::union([Type::Nil, Type::Object]);
                return signature;
            }
            if !return_type.is_never() {
                override_type = override_type.join(return_type);
            }
        }
        if found_override {
            signature.return_type = if override_type.is_never() {
                Type::union([Type::Nil, Type::Object])
            } else {
                override_type
            };
        }
        signature
    }

    pub(super) fn widen_overridable_literal_return(
        &self,
        key: &MethodKey,
        mut signature: MethodSig,
    ) -> MethodSig {
        if !matches!(signature.return_type, Type::True | Type::False) {
            return signature;
        }
        let Some(resolved) = self.resolve_method_key(key) else {
            return signature;
        };
        if !self.declarations.methods.contains_key(&resolved) {
            return signature;
        }
        let Some(owner) = resolved.owner.as_deref() else {
            return signature;
        };
        let overridden = self.declarations.methods.keys().any(|candidate| {
            candidate.singleton == resolved.singleton
                && candidate.name == resolved.name
                && candidate.owner.as_deref().is_some_and(|candidate_owner| {
                    candidate_owner != owner
                        && self.nominal_subtype_names(
                            nominal_name(candidate_owner),
                            nominal_name(owner),
                        )
                })
        });
        if overridden {
            signature.return_type = Type::bool();
        }
        signature
    }
}
