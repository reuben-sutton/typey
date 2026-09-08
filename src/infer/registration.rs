//! Declaration registration and signature validation.
//!
//! This layer builds the workspace declaration graph and validates
//! declaration-time contracts before expression inference begins.

use super::*;

impl<'src> Analyzer<'src> {
    fn validate_rbs_parameter_kinds(
        &mut self,
        offset: usize,
        ruby_parameters: &[(String, signature::ParameterKind)],
        signature: &MethodSig,
    ) {
        for ((name, ruby_kind), rbs_kind) in ruby_parameters.iter().zip(&signature.parameter_kinds)
        {
            if ruby_kind == rbs_kind {
                continue;
            }
            self.reporting.diagnostics.push(Diagnostic::error(
                self.source,
                format!(
                    "Argument kind mismatch for `{name}`, method declares `{}`, but RBS signature declares `{}`",
                    ruby_kind.display_name(),
                    rbs_kind.display_name(),
                ),
                offset,
                offset,
            ));
        }
    }

    fn validate_sorbet_parameter_names(
        &mut self,
        definition_offset: usize,
        signature_offset: usize,
        ruby_parameters: &ParameterShape,
        signature: &MethodSig,
    ) {
        for name in &signature.param_names {
            let matches_definition = ruby_parameters
                .parameter_kinds
                .iter()
                .any(|(defined, _)| defined == name)
                || (name == "&"
                    && ruby_parameters.has_block
                    && ruby_parameters.block_name.is_none());
            if !matches_definition {
                self.reporting.diagnostics.push(Diagnostic::error(
                    self.source,
                    format!("Unknown parameter name `{name}`"),
                    signature_offset,
                    signature_offset,
                ));
            }
        }

        if let Some(block_name) = ruby_parameters.block_name.as_deref() {
            if signature.param_names.iter().any(|name| name == "&")
                && !signature.param_names.iter().any(|name| name == block_name)
            {
                self.reporting.diagnostics.push(Diagnostic::error(
                    self.source,
                    format!("Malformed `sig`. Type not specified for parameter `{block_name}`"),
                    definition_offset,
                    definition_offset,
                ));
            }
        }
    }

    pub(super) fn register_methods<'node>(&mut self, root: &Node<'node>) {
        self.declarations.methods.clear();
        self.declarations.type_aliases = self.annotations.type_aliases.clone();
        let mut registrar = MethodRegistrar::new(
            self.source,
            &mut self.reporting.diagnostics,
            &mut self.declarations,
            &self.annotations.attribute_annotations,
            &self.annotations.class_type_parameters,
        );
        registrar.visit(root);
        self.normalize_class_graph();

        // `class Result < Struct.new(:status, :message)` creates a concrete
        // struct subclass with a generated initializer. Keep the generated
        // constructor and fields in the workspace graph just as for
        // `Result = Struct.new(...)`.
        let struct_subclasses = self
            .declarations
            .classes
            .iter()
            .filter_map(|(owner, info)| {
                info.struct_fields
                    .as_ref()
                    .map(|fields| (owner.clone(), fields.clone()))
            })
            .collect::<Vec<_>>();
        for (owner, fields) in struct_subclasses {
            self.declarations
                .struct_fields
                .insert(owner.clone(), fields.clone());
            for field in &fields {
                let reader = MethodKey {
                    owner: Some(owner.clone()),
                    name: field.clone(),
                    singleton: false,
                };
                self.declarations
                    .accessors
                    .entry(reader.clone())
                    .or_insert(AccessorKind::Reader);
                self.declarations
                    .methods
                    .entry(reader)
                    .or_insert_with(|| MethodState::inferred_accessor(AccessorKind::Reader));

                let writer = MethodKey {
                    owner: Some(owner.clone()),
                    name: format!("{field}="),
                    singleton: false,
                };
                self.declarations
                    .accessors
                    .entry(writer.clone())
                    .or_insert(AccessorKind::Writer);
                self.declarations
                    .methods
                    .entry(writer)
                    .or_insert_with(|| MethodState::inferred_accessor(AccessorKind::Writer));
            }
            let key = MethodKey {
                owner: Some(owner),
                name: "initialize".to_owned(),
                singleton: false,
            };
            self.declarations.methods.entry(key).or_insert_with(|| {
                let mut state = MethodState::inferred(None);
                state.params = vec![Some(Type::Any); fields.len()];
                state.required_params = fields.len();
                state.return_type = Some(Type::Nil);
                state
            });
        }

        // Attribute annotations are registered while walking the AST, before
        // the analyzer has its final class table. Resolve their relative
        // names just like method annotations once all declarations are known.
        let accessor_keys = self
            .declarations
            .accessors
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for key in accessor_keys {
            let Some(signatures) = self
                .declarations
                .methods
                .get(&key)
                .filter(|state| state.explicit)
                .map(|state| state.overloads.clone())
            else {
                continue;
            };
            let signatures = signatures
                .iter()
                .map(|signature| self.resolve_signature_names(signature, key.owner.as_deref()))
                .collect::<Vec<_>>();
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                *state = MethodState::explicit_overloads(&signatures);
            }
        }

        // Resolve annotation offsets through the same definition table used by
        // body evaluation. This makes signatures owner-aware and prevents a
        // method called `remove` (or `initialize`) in one file from changing a
        // same-named method elsewhere in a workspace.
        let mut source_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let mut rbi_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let mut builtin_rbi_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let method_annotations = self.annotations.method_annotations.clone();
        let method_annotation_spans = self.annotations.method_annotation_spans.clone();
        for (offset, signatures) in &method_annotations {
            let Some(key) = self.declarations.definitions.get(offset).cloned() else {
                continue;
            };
            let raw_signatures = signatures.clone();
            let signatures = signatures
                .iter()
                .map(|signature| {
                    let signature = self.declarations.parameter_shapes.get(offset).map_or_else(
                        || signature.clone(),
                        |shape| apply_parameter_shape(signature, shape),
                    );
                    self.resolve_signature_names(&signature, key.owner.as_deref())
                })
                .collect::<Vec<_>>();
            let ruby_parameter_kinds = self
                .declarations
                .parameter_shapes
                .get(offset)
                .map(|shape| shape.parameter_kinds.clone());
            let is_source_annotation = !self
                .rbi_ranges
                .iter()
                .chain(&self.builtin_rbi_ranges)
                .any(|(start, end)| *offset >= *start && *offset < *end);
            if is_source_annotation {
                if let Some(ruby_parameter_kinds) = ruby_parameter_kinds.as_deref() {
                    for signature in &signatures {
                        if !signature.parameter_kinds.is_empty() {
                            self.validate_rbs_parameter_kinds(
                                *offset,
                                ruby_parameter_kinds,
                                signature,
                            );
                        }
                    }
                }
                if let Some(shape) = self.declarations.parameter_shapes.get(offset).cloned() {
                    for (index, signature) in raw_signatures.iter().enumerate() {
                        if !signature.param_names.is_empty() {
                            let signature_offset = method_annotation_spans
                                .get(offset)
                                .and_then(|spans| spans.get(index))
                                .map_or(*offset, |(start, _)| *start);
                            self.validate_sorbet_parameter_names(
                                *offset,
                                signature_offset,
                                &shape,
                                signature,
                            );
                        }
                    }
                }
            }
            if is_source_annotation {
                for (index, signature) in signatures.iter().enumerate() {
                    let signature_offset = method_annotation_spans
                        .get(offset)
                        .and_then(|spans| spans.get(index))
                        .map_or(*offset, |(start, _)| *start);
                    self.validate_attached_class_signature(signature_offset, &key, signature);
                }
            }
            let target = if self
                .builtin_rbi_ranges
                .iter()
                .any(|(start, end)| *offset >= *start && *offset < *end)
            {
                &mut builtin_rbi_signatures
            } else if self
                .rbi_ranges
                .iter()
                .any(|(start, end)| *offset >= *start && *offset < *end)
            {
                &mut rbi_signatures
            } else {
                &mut source_signatures
            };
            target.entry(key.clone()).or_default().extend(signatures);
        }
        for (key, signatures) in source_signatures.into_iter().chain(rbi_signatures) {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit {
                    *state = MethodState::explicit_overloads(&signatures);
                }
            }
        }
        for (key, signatures) in builtin_rbi_signatures {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit {
                    *state = MethodState::explicit_overloads(&signatures);
                }
            }
        }

        // An RBI declaration without a signature is an external method, not
        // a method whose return type is known to be bottom. `MethodState`
        // uses `None`/`Never` provisionally for unresolved source methods so
        // convergence can fill them in later, but an empty RBI body has no
        // implementation for the worklist to analyze. Seed those declarations
        // with Sorbet's gradual fallback instead of leaking `T.noreturn` into
        // callers and making ordinary branches appear unreachable.
        let rbi_definition_keys = self
            .declarations
            .definitions
            .iter()
            .filter(|(offset, _)| self.is_rbi_offset(**offset))
            .map(|(_, key)| key.clone())
            .collect::<BTreeSet<_>>();
        for key in rbi_definition_keys {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit && state.return_type.is_none() {
                    state.return_type = Some(Type::Any);
                }
            }
        }

        self.rebuild_nominal_name_indexes();
    }

    pub(super) fn contains_attached_class_type(type_: &Type) -> bool {
        match type_ {
            Type::AttachedClass | Type::AttachedClassOf(_) => true,
            Type::Named(_, arguments) => arguments.iter().any(Self::contains_attached_class_type),
            Type::Array(element) => Self::contains_attached_class_type(element),
            Type::Hash(key, value) => {
                Self::contains_attached_class_type(key) || Self::contains_attached_class_type(value)
            }
            Type::Tuple(elements) | Type::Union(elements) | Type::Intersection(elements) => {
                elements.iter().any(Self::contains_attached_class_type)
            }
            Type::Proc(parameters, result) => {
                parameters.iter().any(Self::contains_attached_class_type)
                    || Self::contains_attached_class_type(result)
            }
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => {
                Self::contains_attached_class_type(receiver)
                    || parameters.iter().any(Self::contains_attached_class_type)
                    || Self::contains_attached_class_type(result)
            }
            _ => false,
        }
    }

    pub(super) fn attached_class_context_is_valid(&self, key: &MethodKey) -> bool {
        let Some(owner) = key.owner.as_deref() else {
            return false;
        };
        let Some(info) = self.declarations.classes.get(owner) else {
            return false;
        };
        (key.singleton && !info.is_module)
            || (!key.singleton && info.is_module && info.attached_class_member.is_some())
    }

    fn validate_attached_class_signature(
        &mut self,
        offset: usize,
        key: &MethodKey,
        signature: &MethodSig,
    ) {
        let has_in_parameters = signature
            .params
            .iter()
            .any(Self::contains_attached_class_type)
            || signature
                .keywords
                .values()
                .any(|parameter| Self::contains_attached_class_type(&parameter.type_));
        let has_in_return = Self::contains_attached_class_type(&signature.return_type);
        let has_in_block = signature
            .block
            .as_ref()
            .is_some_and(Self::contains_attached_class_type);
        if !has_in_parameters && !has_in_return && !has_in_block {
            return;
        }

        let owner = key.owner.as_deref().unwrap_or("the module");
        let info = self.declarations.classes.get(owner);
        let is_module = info.is_some_and(|info| info.is_module);
        let has_attached_class = info.is_some_and(|info| info.attached_class_member.is_some());
        let message = if key.singleton && is_module {
            Some(
                "`T.attached_class` cannot be used in singleton methods on modules, because modules cannot be instantiated"
                    .to_owned(),
            )
        } else if !key.singleton && is_module && !has_attached_class {
            Some(format!(
                "`{owner}` must declare `has_attached_class!` before module instance methods can use `T.attached_class`"
            ))
        } else if !key.singleton && !is_module {
            Some(
                "`T.attached_class` may only be used in singleton methods on classes or instance methods on `has_attached_class!` modules"
                    .to_owned(),
            )
        } else if has_in_parameters {
            Some("`T.attached_class` may only be used in an `:out` context".to_owned())
        } else {
            None
        };
        let Some(message) = message else {
            return;
        };
        // The signature span is already the source location of the `sig`
        // call. Do not search backwards for the type text: upstream fixtures
        // place expectation comments between the signature and definition,
        // and that search can accidentally select `T.attached_class` from a
        // prose comment instead of the declaration being validated.
        let start = offset.min(self.source.len());
        let end = self
            .source
            .get(start..)
            .and_then(|source| source.iter().position(|byte| *byte == b'\n'))
            .map_or(self.source.len(), |line_end| start + line_end);
        self.reporting
            .diagnostics
            .push(Diagnostic::error(self.source, message, start, end));
    }
}
