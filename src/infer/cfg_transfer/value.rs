//! Owned value, read, and predicate transfer for CFG/HIR.

use super::super::{ivar_refinement_key, Analyzer, Environment, Eval, SharedKey, SourceSite};
use super::globals::cfg_global_refinement_key;
use crate::hir::{self, ArrayElement, ExprKind, HashElement, Literal, Read};
use crate::types::Type;

impl<'src> Analyzer<'src> {
    pub(in crate::infer) fn owned_value_tree_supported(
        program: &hir::Program,
        expression: hir::ExprId,
    ) -> bool {
        let Some(expression) = program.expression(expression) else {
            return false;
        };
        match &expression.kind {
            ExprKind::Nil | ExprKind::Literal(_) | ExprKind::Read(_) => true,
            ExprKind::Array(elements) => elements.iter().all(|element| match element {
                ArrayElement::Value(value) | ArrayElement::Splat { value, .. } => {
                    Self::owned_value_tree_supported(program, *value)
                }
            }),
            ExprKind::Hash(elements) => elements.iter().all(|element| match element {
                HashElement::Pair { key, value } => {
                    Self::owned_value_tree_supported(program, *key)
                        && Self::owned_value_tree_supported(program, *value)
                }
                HashElement::Splat { value, .. } => {
                    Self::owned_value_tree_supported(program, *value)
                }
            }),
            _ => false,
        }
    }

    pub(in crate::infer) fn eval_owned_value(
        &mut self,
        expression: hir::ExprId,
        environment: &mut Environment,
    ) -> Eval {
        let (span, kind) = {
            let expression = self
                .program
                .hir_program
                .expression(expression)
                .expect("owned value expression exists after preflight");
            (expression.span, expression.kind.clone())
        };
        let site = SourceSite::from_span(span, Some(expression));
        let type_ = match kind {
            ExprKind::Nil => Type::Nil,
            ExprKind::Literal(literal) => Self::cfg_literal_type(&literal),
            ExprKind::Read(read) => {
                let type_ = self.transfer_cfg_read_at(site, read, environment);
                return Eval::value(self.record_at(site, type_, false, None));
            }
            ExprKind::Array(elements) => return self.eval_owned_array(site, elements, environment),
            ExprKind::Hash(elements) => return self.eval_owned_hash(site, elements, environment),
            _ => unreachable!("non-value HIR operation reached owned value transfer"),
        };
        let type_ = self.apply_inline_assertion_in_environment_at(site, type_, environment);
        Eval::value(self.record_at(site, type_, false, None))
    }

    fn eval_owned_array(
        &mut self,
        site: SourceSite,
        elements: Vec<ArrayElement>,
        environment: &mut Environment,
    ) -> Eval {
        let tuple_depth = self.literal_tuple_depth;
        self.literal_tuple_depth += 1;
        let mut element_types = Vec::new();
        let mut fixed_length = true;
        let mut element = Type::Never;
        for element_value in elements {
            let (value, splat, splat_span) = match element_value {
                ArrayElement::Value(value) => (value, false, None),
                ArrayElement::Splat { value, span } => (value, true, Some(span)),
            };
            let child_type = self.eval_owned_value(value, environment).type_;
            if let Some(span) = splat_span {
                self.record_at(
                    SourceSite::from_span(span, None),
                    child_type.clone(),
                    false,
                    None,
                );
            }
            let child_type = if splat {
                fixed_length = false;
                self.array_element_type(&child_type)
            } else {
                child_type
            };
            element_types.push(child_type.clone());
            element = element.join(&child_type);
        }
        self.literal_tuple_depth = tuple_depth;
        let element = if element.is_never() {
            if (self.preserve_literal_tuples || self.preserve_nested_literal_tuples)
                && tuple_depth > 0
            {
                Type::Never
            } else {
                Type::Any
            }
        } else {
            element
        };
        let inferred = if fixed_length
            && ((self.preserve_literal_tuples && tuple_depth == 0)
                || (self.preserve_nested_literal_tuples && tuple_depth > 0)
                || self.expected_return_type.as_ref().is_some_and(|expected| {
                    tuple_depth == 0
                        && matches!(expected, Type::Tuple(elements) if elements.len() == element_types.len())
                }))
        {
            Type::Tuple(element_types)
        } else {
            Type::Array(Box::new(element))
        };
        let type_ = self.apply_inline_assertion_in_environment_at(site, inferred, environment);
        Eval::value(self.record_at(site, type_, false, None))
    }

    fn eval_owned_hash(
        &mut self,
        site: SourceSite,
        elements: Vec<HashElement>,
        environment: &mut Environment,
    ) -> Eval {
        let mut key = Type::Never;
        let mut value = Type::Never;
        for element in elements {
            match element {
                HashElement::Pair {
                    key: key_id,
                    value: value_id,
                } => {
                    key = key.join(&self.eval_owned_value(key_id, environment).type_);
                    value = value.join(&self.eval_owned_value(value_id, environment).type_);
                }
                HashElement::Splat {
                    value: value_id, ..
                } => match self.eval_owned_value(value_id, environment).type_ {
                    Type::Hash(splat_key, splat_value) => {
                        key = key.join(&splat_key);
                        value = value.join(&splat_value);
                    }
                    Type::Any => {
                        key = Type::Any;
                        value = Type::Any;
                    }
                    _ => {}
                },
            }
        }
        let key = if key.is_never() { Type::Any } else { key };
        let value = if value.is_never() { Type::Any } else { value };
        let type_ = self.apply_inline_assertion_in_environment_at(
            site,
            Type::Hash(Box::new(key), Box::new(value)),
            environment,
        );
        Eval::value(self.record_at(site, type_, false, None))
    }

    pub(super) fn cfg_literal_type(literal: &Literal) -> Type {
        match literal {
            Literal::Nil => Type::Nil,
            Literal::True => Type::True,
            Literal::False => Type::False,
            Literal::Integer(_) => Type::Integer,
            Literal::Float(_) => Type::Float,
            Literal::Rational(_) => Type::named("Rational"),
            Literal::Imaginary(_) => Type::named("Complex"),
            Literal::String(_) | Literal::XString(_) => Type::String,
            Literal::Symbol(_) => Type::Symbol,
            Literal::RegularExpression(_) => Type::named("Regexp"),
        }
    }

    pub(super) fn transfer_cfg_read_at(
        &mut self,
        site: SourceSite,
        read: Read,
        environment: &mut Environment,
    ) -> Type {
        match read {
            Read::Local(local) => {
                let name = self
                    .program
                    .hir_program
                    .local_name(local)
                    .map_or_else(String::new, |name| name.as_str().to_owned());
                self.apply_inline_assertion_in_environment_at(
                    site,
                    environment.get(&name),
                    environment,
                )
            }
            Read::InstanceVariable(name) => {
                let actual = self.ivar_type(environment, name.as_str());
                self.apply_inline_assertion_in_environment_at(site, actual, environment)
            }
            Read::ClassVariable(name) => {
                let actual = self.class_var_type(environment, name.as_str());
                self.apply_inline_assertion_at(site, actual)
            }
            Read::Global(name) => {
                let name = name.as_str().to_owned();
                self.record_shared_read(SharedKey::Global(name.clone()), environment);
                let actual = environment
                    .contains(&cfg_global_refinement_key(&name))
                    .then(|| environment.get(&cfg_global_refinement_key(&name)))
                    .unwrap_or_else(|| self.globals.get(&name).cloned().unwrap_or(Type::Any));
                self.apply_inline_assertion_at(site, actual)
            }
            Read::Constant(path) => {
                let name = path.as_str().to_owned();
                let actual = self.constant_type(environment, &name);
                if self.reports_missing_api_at(site) && !self.constant_is_known(environment, &name)
                {
                    self.error_at(
                        site,
                        format!(
                            "Unable to resolve constant `{}`",
                            name.trim_start_matches("::")
                        ),
                    );
                }
                self.apply_inline_assertion_at(site, actual)
            }
            Read::SelfValue => self.apply_inline_assertion_at(site, environment.self_type.clone()),
            Read::Numbered(number) => {
                self.apply_inline_assertion_at(site, environment.get(&format!("_{number}")))
            }
            Read::It => self.apply_inline_assertion_at(site, environment.get("it")),
            Read::BackReference(_) => self.apply_inline_assertion_at(site, Type::Any),
        }
    }

    /// Apply the common flow refinements for a CFG branch from owned HIR.
    ///
    /// This intentionally covers only facts represented by HIR operands and
    /// the already-computed environment. More elaborate parser predicates
    /// remain on the recursive adapter until their operand contracts are
    /// represented in HIR as well.
    pub(super) fn narrow_cfg_predicate(
        &mut self,
        expression: hir::ExprId,
        environment: &mut Environment,
        truthy: bool,
    ) {
        let Some(kind) = self
            .program
            .hir_program
            .expression(expression)
            .map(|expression| expression.kind.clone())
        else {
            return;
        };
        match kind {
            hir::ExprKind::Sequence(expressions) => {
                if let Some(last) = expressions.last() {
                    self.narrow_cfg_predicate(*last, environment, truthy);
                }
            }
            hir::ExprKind::Read(Read::Local(local)) => {
                self.narrow_cfg_local(local, environment, truthy)
            }
            hir::ExprKind::Read(Read::InstanceVariable(name)) => {
                let name = name.as_str().to_owned();
                let current = self.ivar_type(environment, &name);
                let narrowed = if truthy {
                    current.meet(&current.truthy_part())
                } else {
                    current.meet(&current.falsy_part())
                };
                environment.bind(ivar_refinement_key(&name), narrowed);
            }
            hir::ExprKind::Assign { target, .. } => match target {
                hir::AssignTarget::Local(local) => {
                    self.narrow_cfg_local(local, environment, truthy);
                }
                hir::AssignTarget::InstanceVariable(name) => {
                    let name = name.as_str().to_owned();
                    let current = self.ivar_type(environment, &name);
                    let narrowed = if truthy {
                        current.meet(&current.truthy_part())
                    } else {
                        current.meet(&current.falsy_part())
                    };
                    environment.bind(ivar_refinement_key(&name), narrowed);
                }
                hir::AssignTarget::ClassVariable(_)
                | hir::AssignTarget::Global(_)
                | hir::AssignTarget::Constant(_)
                | hir::AssignTarget::Attribute { .. }
                | hir::AssignTarget::Index { .. } => {}
            },
            hir::ExprKind::Call(call) => {
                if call.name.as_str() == "!" {
                    if let hir::Receiver::Explicit(receiver) = call.receiver {
                        self.narrow_cfg_predicate(receiver, environment, !truthy);
                    }
                    return;
                }
                let argument_id = match call.arguments.first() {
                    None => None,
                    Some(hir::Argument::Positional(value)) => Some(*value),
                    Some(_) => return,
                };
                match call.receiver {
                    hir::Receiver::Explicit(receiver) => {
                        let Some(receiver_kind) = self
                            .program
                            .hir_program
                            .expression(receiver)
                            .map(|expression| expression.kind.clone())
                        else {
                            return;
                        };
                        match receiver_kind {
                            hir::ExprKind::Read(Read::Local(local)) => self.narrow_cfg_call_target(
                                local,
                                &call.name,
                                argument_id,
                                environment,
                                truthy,
                            ),
                            hir::ExprKind::Read(Read::InstanceVariable(name)) => self
                                .narrow_cfg_ivar_call_target(
                                    name.as_str(),
                                    &call.name,
                                    argument_id,
                                    environment,
                                    truthy,
                                ),
                            _ => {}
                        }
                    }
                    hir::Receiver::Implicit
                        if matches!(call.name.as_str(), "is_a?" | "kind_of?" | "instance_of?") =>
                    {
                        if let Some(argument_id) = argument_id {
                            let current = environment.self_type.clone();
                            let expected =
                                self.cfg_predicate_expected_type(argument_id, environment);
                            environment.self_type = if truthy {
                                self.meet_predicate_type(&current, &expected)
                            } else {
                                current.without(&expected)
                            };
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn narrow_cfg_local(&self, local: hir::LocalId, environment: &mut Environment, truthy: bool) {
        let Some(name) = self
            .program
            .hir_program
            .local_name(local)
            .map(|name| name.as_str())
        else {
            return;
        };
        if environment.is_inferred(name) {
            return;
        }
        let current = environment.get(name);
        let narrowed = if truthy {
            current.meet(&current.truthy_part())
        } else {
            current.meet(&current.falsy_part())
        };
        environment.bind(name.to_owned(), narrowed);
        environment.set_known_truthiness(name.to_owned(), truthy);
    }

    fn narrow_cfg_call_target(
        &mut self,
        local: hir::LocalId,
        name: &hir::Name,
        argument: Option<hir::ExprId>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        let Some(local_name) = self
            .program
            .hir_program
            .local_name(local)
            .map(|name| name.as_str().to_owned())
        else {
            return;
        };
        if environment.is_inferred(&local_name) {
            return;
        }
        let current = environment.get(&local_name);
        let argument_type = argument
            .map(|argument| self.cfg_predicate_argument_type(argument, environment))
            .unwrap_or(Type::Any);
        let narrowed = match name.as_str() {
            "nil?" if argument.is_none() => {
                if truthy {
                    current.meet(&Type::Nil)
                } else {
                    current.without(&Type::Nil)
                }
            }
            "is_a?" | "kind_of?" | "instance_of?" if argument.is_some() => {
                if truthy {
                    self.meet_predicate_type(&current, &argument_type)
                } else {
                    current.without(&argument_type)
                }
            }
            "==" | "equal?" | "eql?" if argument.is_some() => {
                if truthy {
                    current.meet(&argument_type)
                } else {
                    current.clone()
                }
            }
            "!=" if argument.is_some() && truthy => {
                if matches!(argument_type, Type::Nil | Type::True | Type::False) {
                    current.without(&argument_type)
                } else {
                    current.clone()
                }
            }
            "!=" if argument.is_some() => current.meet(&argument_type),
            "empty?" if argument.is_none() => {
                if matches!(current, Type::Array(_) | Type::Tuple(_)) {
                    environment.set_known_nonempty_array(&local_name, !truthy);
                }
                return;
            }
            _ => return,
        };
        environment.bind(local_name, narrowed);
    }

    fn narrow_cfg_ivar_call_target(
        &mut self,
        name: &str,
        method: &hir::Name,
        argument: Option<hir::ExprId>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        let current = self.ivar_type(environment, name);
        let argument_type = argument
            .map(|argument| self.cfg_predicate_argument_type(argument, environment))
            .unwrap_or(Type::Any);
        let narrowed = match method.as_str() {
            "nil?" if argument.is_none() => {
                if truthy {
                    current.meet(&Type::Nil)
                } else {
                    current.without(&Type::Nil)
                }
            }
            "is_a?" | "kind_of?" | "instance_of?" if argument.is_some() => {
                if truthy {
                    self.meet_predicate_type(&current, &argument_type)
                } else {
                    current.without(&argument_type)
                }
            }
            _ => return,
        };
        environment.bind(ivar_refinement_key(name), narrowed);
    }

    fn cfg_predicate_argument_type(
        &mut self,
        expression: hir::ExprId,
        environment: &Environment,
    ) -> Type {
        let Some(kind) = self
            .program
            .hir_program
            .expression(expression)
            .map(|expression| expression.kind.clone())
        else {
            return Type::Any;
        };
        match kind {
            hir::ExprKind::Literal(literal) => Self::cfg_literal_type(&literal),
            hir::ExprKind::Read(Read::Constant(path)) => {
                let type_ = self.constant_type(environment, path.as_str());
                Self::class_object_value_type(&type_).unwrap_or(type_)
            }
            hir::ExprKind::Read(Read::Local(local)) => self
                .program
                .hir_program
                .local_name(local)
                .map_or(Type::Any, |name| environment.get(name.as_str())),
            _ => Type::Any,
        }
    }

    fn cfg_predicate_expected_type(
        &mut self,
        expression: hir::ExprId,
        environment: &Environment,
    ) -> Type {
        self.cfg_predicate_argument_type(expression, environment)
    }
}
