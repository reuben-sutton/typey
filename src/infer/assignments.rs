//! HIR assignment transfer and storage updates.
//!
//! This layer adapts lowered assignment targets to the shared send and flow
//! semantics without making the analyzer coordinator own every target kind.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_call_result<'node>(
        &mut self,
        node: &Node<'node>,
        call: &HirCallView<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let mut result = self.eval_call(node, call, environment);
        let type_ =
            self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
        if result.normal_type.is_some() {
            result.normal_type = Some(type_.clone());
        }
        result.type_ = self.record(node, type_);
        result
    }

    fn eval_hir_set_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        call: CallNode<'node>,
        target: &hir::AssignTarget,
        value: hir::ExprId,
        environment: &mut Environment,
    ) -> Eval {
        // Keep the assignment as an owned HIR assignment, but reuse the
        // established setter protocol for its runtime send. The synthetic
        // call is an evaluator adapter only: its receiver and argument shape
        // come from the HIR target, while the source Prism node remains solely
        // the child-expression bridge used by `HirCallView`.
        let (name, receiver, arguments) = match target {
            hir::AssignTarget::Attribute { receiver, name } => (
                format!("{}=", name.as_str()),
                hir::Receiver::Explicit(*receiver),
                vec![hir::Argument::Positional(value)],
            ),
            hir::AssignTarget::Index {
                receiver,
                arguments,
            } => {
                let mut arguments = arguments.clone();
                arguments.push(hir::Argument::Positional(value));
                (
                    "[]=".to_owned(),
                    hir::Receiver::Explicit(*receiver),
                    arguments,
                )
            }
            _ => return Eval::value(self.record(node, Type::Any)),
        };
        let view = HirCallView {
            call: hir::Call {
                receiver,
                name: hir::Name::new(name),
                arguments,
                argument_groups: Vec::new(),
                argument_spans: Vec::new(),
                block: None,
                safe_navigation: false,
                span: hir::Span::new(
                    hir::FileId(0),
                    prism::span(node).0 as u32,
                    prism::span(node).1 as u32,
                ),
            },
            prism_call: call,
        };
        self.eval_call_result(node, &view, environment)
    }

    pub(super) fn eval_hir_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: hir::AssignTarget,
        value_id: hir::ExprId,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        debug_assert!(self.hir_program.expression(value_id).is_some());
        let value_node = self
            .assignment_value_node(node)
            .expect("lowered assignment must retain its value expression");
        match target {
            hir::AssignTarget::Attribute { receiver, name } => {
                let receiver_node = self
                    .assignment_receiver_node(node)
                    .expect("lowered attribute assignment must retain its receiver");
                match operator {
                    hir::AssignOperator::Set => {
                        let call = node
                            .as_call_node()
                            .expect("plain attribute assignment is a call node");
                        self.eval_hir_set_assignment(
                            node,
                            call,
                            &hir::AssignTarget::Attribute { receiver, name },
                            value_id,
                            environment,
                        )
                    }
                    hir::AssignOperator::And => self.eval_call_assignment(
                        node,
                        receiver_node,
                        name.as_str(),
                        &format!("{}=", name.as_str()),
                        value_node,
                        CallAssignmentKind::And,
                        environment,
                    ),
                    hir::AssignOperator::Or => self.eval_call_assignment(
                        node,
                        receiver_node,
                        name.as_str(),
                        &format!("{}=", name.as_str()),
                        value_node,
                        CallAssignmentKind::Or,
                        environment,
                    ),
                    hir::AssignOperator::Binary(operator) => self.eval_call_assignment(
                        node,
                        receiver_node,
                        name.as_str(),
                        &format!("{}=", name.as_str()),
                        value_node,
                        CallAssignmentKind::Operator(operator.as_str().to_owned()),
                        environment,
                    ),
                }
            }
            hir::AssignTarget::Index {
                receiver: hir_receiver,
                arguments: hir_arguments,
            } => match operator {
                hir::AssignOperator::Set => {
                    let call = node
                        .as_call_node()
                        .expect("plain index assignment is a call node");
                    self.eval_hir_set_assignment(
                        node,
                        call,
                        &hir::AssignTarget::Index {
                            receiver: hir_receiver,
                            arguments: hir_arguments,
                        },
                        value_id,
                        environment,
                    )
                }
                operator => {
                    let receiver = self
                        .assignment_receiver_node(node)
                        .expect("lowered index assignment must retain its receiver");
                    let arguments = self
                        .assignment_index_arguments(node)
                        .expect("lowered index assignment must retain its arguments");
                    let kind = match operator {
                        hir::AssignOperator::And => IndexAssignmentKind::And,
                        hir::AssignOperator::Or => IndexAssignmentKind::Or,
                        hir::AssignOperator::Binary(operator) => {
                            IndexAssignmentKind::Operator(operator.as_str().to_owned())
                        }
                        hir::AssignOperator::Set => unreachable!("handled above"),
                    };
                    self.eval_index_assignment(
                        node,
                        receiver,
                        arguments,
                        &hir_arguments,
                        value_node,
                        kind,
                        environment,
                    )
                }
            },
            hir::AssignTarget::Local(local) => {
                let name = self
                    .hir_program
                    .local_name(local)
                    .expect("lowered local target must have a spelling")
                    .as_str()
                    .to_owned();
                self.eval_hir_local_assignment(node, name, value_node, operator, environment)
            }
            hir::AssignTarget::InstanceVariable(name) => self.eval_hir_instance_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
            hir::AssignTarget::ClassVariable(name) => self.eval_hir_class_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
            hir::AssignTarget::Global(name) => self.eval_hir_global_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
            hir::AssignTarget::Constant(name) => self.eval_hir_constant_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
        }
    }

    fn eval_hir_local_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: String,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = self.eval_node(&value_node, environment).normal_type();
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                if let Some(alias) = self.predicate_alias_for_value(&value_node, environment) {
                    environment.bind_predicate_alias(name.clone(), type_.clone(), alias);
                } else {
                    environment.bind(name.clone(), type_.clone());
                }
                if value_node
                    .as_array_node()
                    .is_some_and(|array| array.elements().is_empty())
                    && matches!(&type_, Type::Array(element) if element.is_any())
                {
                    environment.open_array_locals.insert(name);
                }
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let result = self.eval_compound_assignment(
                    environment.get(&name),
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    environment.bind(name.clone(), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                let result =
                    self.eval_and_assignment(environment.get(&name), &value_node, environment);
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    environment.bind(name.clone(), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                let current = environment.get(&name);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = self.eval_node(&value_node, environment).normal_type();
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared =
                    self.apply_inline_assertion_in_environment(node, actual, environment);
                environment.bind(
                    name,
                    if right.without(&Type::Nil) == right {
                        declared.without(&Type::Nil)
                    } else {
                        declared.clone()
                    },
                );
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared
                };
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_instance_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = self.eval_node(&value_node, environment).normal_type();
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                let type_ =
                    self.preserve_typed_empty_array_ivar(environment, name, &value_node, type_);
                let provisional = value_node
                    .as_local_variable_read_node()
                    .is_some_and(|local| {
                        environment.is_provisional(&prism::constant_name(local.name()))
                    });
                self.observe_ivar(environment, name.to_owned(), &type_, provisional);
                environment.bind(ivar_refinement_key(name), type_.clone());
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let current = self.ivar_type(environment, name);
                let result = self.eval_compound_assignment(
                    current,
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    self.observe_ivar(environment, name.to_owned(), &type_, false);
                    environment.bind(ivar_refinement_key(name), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                let current = self.ivar_type(environment, name);
                let result = self.eval_and_assignment(current, &value_node, environment);
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    self.observe_ivar(environment, name.to_owned(), &type_, false);
                    environment.bind(ivar_refinement_key(name), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                let current = self.ivar_type(environment, name);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = self.eval_node(&value_node, environment).normal_type();
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared =
                    self.apply_inline_assertion_in_environment(node, actual, environment);
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared.clone()
                };
                self.observe_ivar(environment, name.to_owned(), &declared, false);
                environment.bind(ivar_refinement_key(name), type_.clone());
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_class_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = self.eval_node(&value_node, environment).normal_type();
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.to_owned(), &type_);
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let current = self.class_var_type(environment, name);
                let result = self.eval_compound_assignment(
                    current,
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_class_var(environment, name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                let current = self.class_var_type(environment, name);
                let result = self.eval_and_assignment(current, &value_node, environment);
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_class_var(environment, name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                let current = self.class_var_type(environment, name);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = self.eval_node(&value_node, environment).normal_type();
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.to_owned(), &declared);
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared
                };
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_global_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = self.eval_node(&value_node, environment).normal_type();
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_global(name.to_owned(), &type_);
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                self.record_shared_read(SharedKey::Global(name.to_owned()), environment);
                let result = self.eval_compound_assignment(
                    self.globals.get(name).cloned().unwrap_or(Type::Any),
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_global(name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                self.record_shared_read(SharedKey::Global(name.to_owned()), environment);
                let result = self.eval_and_assignment(
                    self.globals.get(name).cloned().unwrap_or(Type::Any),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_global(name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                self.record_shared_read(SharedKey::Global(name.to_owned()), environment);
                let current = self.globals.get(name).cloned().unwrap_or(Type::Any);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = self.eval_node(&value_node, environment).normal_type();
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared = self.apply_inline_assertion(node, actual);
                self.observe_global(name.to_owned(), &declared);
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared
                };
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_constant_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = self.eval_node(&value_node, environment).normal_type();
                let struct_type = self.struct_subclass_type(environment, &value_node, name);
                if let Some(struct_type) = struct_type.as_ref() {
                    self.eval_dynamic_struct_block(&value_node, struct_type, environment);
                }
                let type_ = self.apply_inline_assertion(node, struct_type.unwrap_or(actual));
                self.observe_constant(environment, name.to_owned(), &type_);
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let current = self.constant_type(environment, name);
                let result = self.eval_compound_assignment(
                    current,
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                self.finish_hir_constant_operation(node, name, result, environment)
            }
            hir::AssignOperator::And => {
                let current = self.constant_type(environment, name);
                let result = self.eval_and_assignment(current, &value_node, environment);
                self.finish_hir_constant_operation(node, name, result, environment)
            }
            hir::AssignOperator::Or => {
                let current = self.constant_type(environment, name);
                let result = self.eval_or_assignment(current, &value_node, environment);
                self.finish_hir_constant_operation(node, name, result, environment)
            }
        }
    }

    fn finish_hir_constant_operation<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        result: Eval,
        environment: &mut Environment,
    ) -> Eval {
        let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
        let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
        if let Some(type_) = normal_type.as_ref() {
            self.observe_constant(environment, name.to_owned(), type_);
        }
        let mut result = Eval::from_parts(normal_type, abrupt, flow);
        result.type_ = self.record(node, result.type_.clone());
        result
    }
}
