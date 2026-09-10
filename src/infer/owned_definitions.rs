//! Owned transfer for declaration expressions.
//!
//! Declarations are registered before inference, but their Ruby expression
//! still has runtime effects: class/module bodies execute, and a method
//! definition contributes its inferred body summary. Keep those effects in
//! the owned HIR/CFG path rather than making declaration syntax an implicit
//! parser fallback.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_owned_definition(
        &mut self,
        declaration_id: hir::DeclId,
        context_type: Option<Type>,
        outer: &mut Environment,
    ) -> Result<Type, String> {
        let declaration = self
            .program
            .hir_program
            .declaration(declaration_id)
            .cloned()
            .ok_or_else(|| format!("missing HIR declaration {declaration_id:?}"))?;
        match declaration.kind {
            hir::DeclarationKind::Method {
                name,
                singleton,
                body,
            } => {
                self.eval_owned_method_definition(declaration.span, name, singleton, body, outer)?;
            }
            hir::DeclarationKind::Class {
                name,
                superclass: _,
                body,
            } => {
                self.eval_owned_namespace_body(declaration.span, name.as_str(), body, outer)?;
            }
            hir::DeclarationKind::Module { name, body } => {
                self.eval_owned_namespace_body(declaration.span, name.as_str(), body, outer)?;
            }
            hir::DeclarationKind::SingletonClass {
                expression: _,
                body,
            } => {
                let expression_type = context_type.unwrap_or_else(|| outer.self_type.clone());
                self.eval_owned_singleton_body(declaration.span, expression_type, body, outer)?;
            }
        }
        Ok(Type::Nil)
    }

    fn eval_owned_method_definition(
        &mut self,
        span: hir::Span,
        name: hir::Name,
        singleton: bool,
        body: hir::BodyId,
        outer: &mut Environment,
    ) -> Result<(), String> {
        // RBI method bodies are declaration placeholders, not executable
        // application code. Their signatures are registered above; executing
        // bodies such as `def call(*args, **, &block); end` would only create
        // CFG fallback noise for syntax that has no runtime semantics here.
        if self.is_rbi_offset(span.start as usize) {
            return Ok(());
        }
        let registered_key = self
            .declarations
            .definitions
            .get(&(span.start as usize))
            .cloned()
            .unwrap_or(MethodKey {
                owner: None,
                name: name.as_str().to_owned(),
                singleton,
            });
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
            return Ok(());
        }
        self.begin_method_evaluation(&key);
        let previous_substitution_context = self.substitution_context.replace(key.clone());
        let state = self
            .declarations
            .methods
            .get(&key)
            .cloned()
            .unwrap_or_else(|| {
                self.program
                    .hir_program
                    .body(body)
                    .map(|body| MethodState::inferred_hir(&body.parameters))
                    .unwrap_or_else(|| MethodState::inferred(None))
            });
        let self_type = key.owner.as_ref().map_or(Type::Object, |owner| {
            if key.singleton {
                Self::class_object_type(owner)
            } else if self.is_concern_class_methods_module(owner) {
                Type::Any
            } else {
                self.instance_self_type(owner)
            }
        });
        let mut method_environment = Environment {
            self_type,
            method_key: Some(key.clone()),
            ..Environment::default()
        };
        let body_signature = self.substitute_method_signature(
            &state.body_signature(),
            Some(&method_environment.self_type),
        );
        let parameters = self
            .program
            .hir_program
            .body(body)
            .map(|body| body.parameters.clone())
            .ok_or_else(|| format!("missing method body {body:?}"))?;
        self.bind_owned_parameters(
            &parameters,
            &body_signature,
            &state,
            &mut method_environment,
        );
        for parameter in &parameters.parameters {
            let Some(default_body) = parameter.default_body else {
                continue;
            };
            // A default is evaluated only on the path where its argument is
            // omitted. Analyze it in a fork so calls and shared dependencies
            // are published, while local effects join the method's normal
            // entry state instead of becoming unconditional assignments.
            let mut default_environment = method_environment.clone();
            self.eval_cfg_body_owned(
                self.owned_body_site(default_body),
                default_body,
                &mut default_environment,
                true,
            )
            .ok_or_else(|| "parameter default requires a legacy transfer".to_owned())?;
            method_environment = method_environment.join(&default_environment);
        }

        let previous_expected_return = self.expected_return_type.take();
        self.expected_return_type = if state.explicit && !state.is_void {
            Some(
                self.substitute_method_signature(
                    &state.call_signature(),
                    Some(&method_environment.self_type),
                )
                .return_type,
            )
        } else {
            None
        };
        let body_result = self
            .eval_cfg_body_owned(
                self.owned_body_site(body),
                body,
                &mut method_environment,
                true,
            )
            .ok_or_else(|| "method body requires a legacy transfer".to_owned())?;
        self.expected_return_type = previous_expected_return;
        let inferred_return = body_result.method_return_type();
        if self.fixpoint.collecting_returns {
            self.record_inferred_raise(key.clone(), body_result.abrupt.raise_type.clone());
        }
        if state.explicit
            && !state.is_void
            && !state.is_abstract
            && !self.is_rbi_offset(span.start as usize)
        {
            let expected = self.substitute_method_signature(
                &state.call_signature(),
                Some(&method_environment.self_type),
            );
            let invalid_attached_class_context =
                (Self::contains_attached_class_type(&expected.return_type)
                    || expected
                        .params
                        .iter()
                        .any(Self::contains_attached_class_type))
                    && !self.attached_class_context_is_valid(&key);
            if !invalid_attached_class_context
                && !inferred_return.is_never()
                && !self.is_assignable(&inferred_return, &expected.return_type)
            {
                self.error_at(
                    SourceSite::from_span(span, None),
                    format!(
                        "Expected method `{}` to return `{}`, but found `{}`",
                        name.as_str(),
                        expected.return_type,
                        inferred_return
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
        Ok(())
    }

    fn bind_owned_parameters(
        &self,
        parameters: &hir::Parameters,
        signature: &MethodSig,
        state: &MethodState,
        environment: &mut Environment,
    ) {
        let mut positional = 0;
        for parameter in &parameters.parameters {
            let local_name = parameter
                .local
                .and_then(|local| self.program.hir_program.local_name(local))
                .map(|name| name.as_str().to_owned());
            match parameter.kind {
                hir::ParameterKind::Required
                | hir::ParameterKind::Optional
                | hir::ParameterKind::Post => {
                    if let Some(name) = local_name {
                        environment.bind(
                            name.clone(),
                            signature
                                .params
                                .get(positional)
                                .cloned()
                                .unwrap_or(Type::Any),
                        );
                        if !state.explicit {
                            environment.mark_inferred(name);
                        }
                    }
                    positional += 1;
                }
                hir::ParameterKind::Rest => {
                    if let Some(name) = local_name {
                        let element = signature
                            .params
                            .get(positional)
                            .cloned()
                            .unwrap_or(Type::Any);
                        environment.bind(name.clone(), Type::Array(Box::new(element)));
                        if !state.explicit {
                            environment.mark_inferred(name);
                        }
                    }
                    positional += 1;
                }
                hir::ParameterKind::RequiredKeyword | hir::ParameterKind::OptionalKeyword => {
                    if let Some(name) = parameter.name.as_ref().map(|name| name.as_str()) {
                        let type_ = signature
                            .keywords
                            .get(name)
                            .map(|parameter| parameter.type_.clone())
                            .unwrap_or(Type::Any);
                        environment.bind(name.to_owned(), type_);
                        if !state.explicit {
                            environment.mark_inferred(name.to_owned());
                        }
                    }
                }
                hir::ParameterKind::KeywordRest => {
                    if let Some(name) = local_name {
                        environment.bind(
                            name.clone(),
                            Type::Hash(Box::new(Type::Symbol), Box::new(Type::Any)),
                        );
                        if !state.explicit {
                            environment.mark_inferred(name);
                        }
                    }
                }
                hir::ParameterKind::Block => {
                    if let Some(name) = local_name {
                        let block = signature.block.clone().unwrap_or_else(|| {
                            Type::Proc(
                                state.block_parameters(),
                                Box::new(state.block_result_type()),
                            )
                        });
                        let block = if state.explicit {
                            block
                        } else {
                            Type::union([Type::Nil, block])
                        };
                        environment.bind(name.clone(), block);
                        if !state.explicit {
                            environment.mark_inferred(name);
                        }
                    }
                }
                hir::ParameterKind::Forwarded | hir::ParameterKind::Anonymous => {}
            }
        }
    }

    fn eval_owned_namespace_body(
        &mut self,
        span: hir::Span,
        raw_name: &str,
        body: Option<hir::BodyId>,
        outer: &mut Environment,
    ) -> Result<(), String> {
        if self.seed_calls || self.is_rbi_offset(span.start as usize) {
            return Ok(());
        }
        let Some(body) = body else {
            return Ok(());
        };
        let name = self.scoped_constant_name(outer, raw_name);
        let mut namespace_environment = outer.clone();
        namespace_environment.self_type = Self::class_object_type(&name);
        let key = MethodKey {
            owner: Some(name),
            name: "<class-body>".to_owned(),
            singleton: true,
        };
        namespace_environment.method_key = Some(key.clone());
        let previous_substitution_context = self.substitution_context.replace(key);
        let result = self
            .eval_cfg_body_owned(
                self.owned_body_site(body),
                body,
                &mut namespace_environment,
                true,
            )
            .is_some();
        self.substitution_context = previous_substitution_context;
        result
            .then_some(())
            .ok_or_else(|| "namespace body requires a legacy transfer".to_owned())
    }

    fn eval_owned_singleton_body(
        &mut self,
        span: hir::Span,
        expression_type: Type,
        body: Option<hir::BodyId>,
        outer: &mut Environment,
    ) -> Result<(), String> {
        if self.seed_calls || self.is_rbi_offset(span.start as usize) {
            return Ok(());
        }
        let Some(body) = body else {
            return Ok(());
        };
        let owner = Self::class_object_owner(&expression_type);
        let mut singleton_environment = outer.clone();
        singleton_environment.self_type = expression_type;
        singleton_environment.method_key = Some(MethodKey {
            owner,
            name: "<singleton-body>".to_owned(),
            singleton: true,
        });
        let result = self
            .eval_cfg_body_owned(
                self.owned_body_site(body),
                body,
                &mut singleton_environment,
                true,
            )
            .is_some();
        result
            .then_some(())
            .ok_or_else(|| "singleton body requires a legacy transfer".to_owned())
    }
}
