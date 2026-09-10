use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_statements<'node>(
        &mut self,
        statements: &ruby_prism::StatementsNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let mut flow = Flow::normal();
        let mut normal_type = Some(Type::Nil);
        let mut abrupt = OutcomeTypes::default();
        let body = statements.body();
        let report_unreachable = environment.method_key.is_some();
        for child in &body {
            if flow.is_terminated() {
                if report_unreachable {
                    self.error(
                        &child,
                        "This expression appears after an unconditional return",
                    );
                }
                // Sorbet still traverses dead method/closure syntax for
                // source/type accounting, but does not report ordinary
                // missing-method or contract errors from a path that cannot
                // execute. Top-level expressions remain independently
                // reportable after a `T.noreturn` expression.
                if report_unreachable {
                    let previous_suppression = self.reporting.suppress_diagnostics;
                    self.reporting.suppress_diagnostics = true;
                    let _ = self.eval_node(&child, environment);
                    self.reporting.suppress_diagnostics = previous_suppression;
                } else {
                    let _ = self.eval_node(&child, environment);
                }
                continue;
            }
            let result = self.eval_node(&child, environment);
            abrupt = abrupt.join(&result.abrupt);
            flow = flow.without(FlowKind::Normal).union(result.flow);
            normal_type = result.normal_type;
            if result.flow.is_terminated() {
                normal_type = None;
            }
        }
        Eval::from_parts(normal_type, abrupt, flow)
    }

    pub(super) fn eval_compound_assignment<'node>(
        &mut self,
        receiver: Type,
        operator: &str,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let value_result = self.eval_node(value_node, environment);
        let Some(value_type) = value_result.normal_type.clone() else {
            return value_result;
        };
        let site = CallSite {
            argument_nodes: std::slice::from_ref(value_node),
            argument_types: std::slice::from_ref(&value_type),
            block: None,
        };
        let result_type = self.eval_method_call(&receiver, operator, &site, environment);
        Eval::from_parts(Some(result_type), value_result.abrupt, value_result.flow)
    }

    pub(super) fn eval_call_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        receiver_node: Option<Node<'node>>,
        read_name: &str,
        write_name: &str,
        value_node: Node<'node>,
        kind: CallAssignmentKind,
        environment: &mut Environment,
    ) -> Eval {
        let receiver_result = if let Some(receiver) = receiver_node.as_ref() {
            self.eval_node(receiver, environment)
        } else {
            Eval::value(environment.self_type.clone())
        };
        let receiver_type = receiver_result.normal_type.clone().unwrap_or(Type::Never);
        let getter_site = CallSite {
            argument_nodes: &[],
            argument_types: &[],
            block: None,
        };
        let current = self.eval_method_call(&receiver_type, read_name, &getter_site, environment);
        let value_result = match kind {
            CallAssignmentKind::Operator(operator) => {
                self.eval_compound_assignment(current, &operator, &value_node, environment)
            }
            CallAssignmentKind::And => self.eval_and_assignment(current, &value_node, environment),
            CallAssignmentKind::Or => self.eval_or_assignment(current, &value_node, environment),
        };
        if let Some(value_type) = value_result.normal_type.as_ref() {
            let setter_site = CallSite {
                argument_nodes: std::slice::from_ref(&value_node),
                argument_types: std::slice::from_ref(value_type),
                block: None,
            };
            let _ = self.eval_method_call(&receiver_type, write_name, &setter_site, environment);
        }
        let normal_type = receiver_result
            .normal_type
            .is_some()
            .then_some(value_result.normal_type.clone())
            .flatten();
        let mut result = Eval::from_parts(
            normal_type,
            receiver_result.abrupt.join(&value_result.abrupt),
            receiver_result.flow.union(value_result.flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    pub(super) fn eval_and_assignment<'node>(
        &mut self,
        current: Type,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let truthy = current.truthy_part();
        let mut right_environment = environment.clone();
        let right = if truthy.is_never() {
            Eval::unreachable()
        } else {
            self.eval_node(value_node, &mut right_environment)
        };
        if !truthy.is_never() {
            *environment = environment.join(&right_environment);
        }
        let normal_type = Type::union([
            current.falsy_part(),
            right.normal_type.clone().unwrap_or(Type::Never),
        ]);
        let normal_type = (!normal_type.is_never()).then_some(normal_type);
        let abrupt = if truthy.is_never() {
            OutcomeTypes::default()
        } else {
            right.abrupt
        };
        let flow = if normal_type.is_some() {
            Flow::normal().union(abrupt.flow())
        } else {
            abrupt.flow()
        };
        Eval::from_parts(normal_type, abrupt, flow)
    }

    pub(super) fn eval_or_assignment<'node>(
        &mut self,
        current: Type,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let falsy = current.falsy_part();
        let mut right_environment = environment.clone();
        let right = if falsy.is_never() {
            Eval::unreachable()
        } else {
            self.eval_node(value_node, &mut right_environment)
        };
        if !falsy.is_never() {
            *environment = environment.join(&right_environment);
        }
        let normal_type = Type::union([
            current.truthy_part(),
            right.normal_type.clone().unwrap_or(Type::Never),
        ]);
        let normal_type = (!normal_type.is_never()).then_some(normal_type);
        let abrupt = if falsy.is_never() {
            OutcomeTypes::default()
        } else {
            right.abrupt
        };
        let flow = if normal_type.is_some() {
            Flow::normal().union(abrupt.flow())
        } else {
            abrupt.flow()
        };
        Eval::from_parts(normal_type, abrupt, flow)
    }

    pub(super) fn eval_index_access<'node>(
        &mut self,
        receiver_node: Option<&Node<'node>>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        hir_arguments: &[hir::Argument],
        environment: &mut Environment,
    ) -> IndexAccess<'node> {
        let receiver_result = receiver_node.as_ref().map_or_else(
            || Eval::value(Type::Object),
            |receiver| self.eval_node(receiver, environment),
        );
        let argument_inputs = hir_call_argument_inputs(hir_arguments, arguments);
        let evaluated = self.evaluate_call_arguments(argument_inputs, environment);
        let receiver_type = receiver_result.normal_type.clone().unwrap_or(Type::Never);
        IndexAccess {
            receiver_type,
            arguments: evaluated.arguments,
            abrupt: receiver_result.abrupt.join(&evaluated.abrupt),
            abrupt_flow: receiver_result
                .flow
                .without(FlowKind::Normal)
                .union(evaluated.abrupt_flow),
            all_normal: receiver_result.normal_type.is_some() && evaluated.all_normal,
        }
    }

    pub(super) fn eval_index_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        receiver_node: Option<Node<'node>>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        hir_arguments: &[hir::Argument],
        value_node: Node<'node>,
        kind: IndexAssignmentKind,
        environment: &mut Environment,
    ) -> Eval {
        let access = self.eval_index_access(
            receiver_node.as_ref(),
            arguments,
            hir_arguments,
            environment,
        );
        let current = receiver_node
            .as_ref()
            .and_then(|receiver| {
                self.receiver_method_key(Some(receiver), &access.receiver_type, "[]", environment)
            })
            .and_then(|key| {
                self.eval_resolved_receiver_call(
                    node,
                    "[]",
                    receiver_node.as_ref(),
                    &key,
                    &access.receiver_type,
                    &access.arguments,
                    None,
                    environment,
                )
                .map(|(type_, _)| type_)
            })
            .unwrap_or_else(|| {
                let site = CallSite {
                    argument_nodes: &access.arguments.argument_nodes,
                    argument_types: &access.arguments.argument_types,
                    block: None,
                };
                self.eval_method_call(&access.receiver_type, "[]", &site, environment)
            });
        let value_result = match kind {
            IndexAssignmentKind::Operator(operator) => self.eval_compound_assignment(
                current.without(&Type::Nil),
                &operator,
                &value_node,
                environment,
            ),
            IndexAssignmentKind::And => self.eval_and_assignment(current, &value_node, environment),
            IndexAssignmentKind::Or => self.eval_or_assignment(current, &value_node, environment),
        };
        let normal_type = if access.all_normal {
            value_result.normal_type
        } else {
            None
        };
        let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
        let abrupt = access.abrupt.join(&value_result.abrupt);
        let flow = access
            .abrupt_flow
            .union(value_result.flow.without(FlowKind::Normal));
        let flow = if normal_type.is_some() {
            Flow::normal().union(flow)
        } else {
            flow
        };
        let mut result = Eval::from_parts(normal_type, abrupt, flow);
        result.type_ = self.record(node, result.type_.clone());
        result
    }

    pub(super) fn eval_node<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if !self.defer_inline_assertions {
            if let Some(assertion) = self.inline_assertion_for_node(node) {
                if assertion.kind == AssertionKind::SelfAs {
                    let previous_self_type = environment.self_type.clone();
                    environment.self_type = self.resolve_type_names(
                        &assertion.type_,
                        self.lexical_owner(environment).as_deref(),
                    );
                    let result = self.eval_node_inner(node, environment);
                    environment.self_type = previous_self_type;
                    return result;
                }
            }
        }
        self.eval_node_inner(node, environment)
    }

    pub(super) fn eval_node_inner<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if self.config.debug {
            self.fixpoint.debug_nodes += 1;
            if self
                .fixpoint
                .debug_nodes
                .is_multiple_of(DEBUG_NODE_INTERVAL)
            {
                let (start, _) = prism::span(node);
                if self.fixpoint.debug_round == 0 {
                    eprintln!(
                        "[typey] {} pass: visited {} nodes (source offset {})",
                        self.fixpoint.debug_phase, self.fixpoint.debug_nodes, start
                    );
                } else {
                    eprintln!(
                        "[typey] fixpoint round {} {} pass: visited {} nodes (source offset {})",
                        self.fixpoint.debug_round,
                        self.fixpoint.debug_phase,
                        self.fixpoint.debug_nodes,
                        start
                    );
                }
            }
        }
        if let Some(program) = node.as_program_node() {
            if self.config.enable_cfg {
                if let Some(body_id) = self.program.hir_body_ids.get(&prism::span(node)).copied() {
                    if let Some(result) = self.eval_cfg_body_owned(
                        self.owned_body_site(body_id),
                        body_id,
                        environment,
                        true,
                    ) {
                        return result;
                    }
                }
            }
            let result = self.eval_statements(&program.statements(), environment);
            return Eval {
                type_: self.record(node, result.type_),
                flow: result.flow,
                normal_type: result.normal_type,
                abrupt: result.abrupt,
            };
        }
        if let Some(statements) = node.as_statements_node() {
            let result = self.eval_statements(&statements, environment);
            return Eval {
                type_: self.record(node, result.type_),
                flow: result.flow,
                normal_type: result.normal_type,
                abrupt: result.abrupt,
            };
        }
        if let Some(definition) = node.as_def_node() {
            return self.eval_definition(node, &definition, environment);
        }
        if let Some(class) = node.as_class_node() {
            if self.seed_calls || self.is_rbi_definition(node) {
                return Eval::value(Type::Nil);
            }
            let class_name = self.scoped_constant_name(
                environment,
                &self
                    .constant_reference_name(&class.constant_path())
                    .unwrap_or_else(|| prism::text(self.program.source, &class.constant_path())),
            );
            if let Some(superclass) = class.superclass() {
                // The registrar models dynamic superclasses such as
                // `Struct.new(...)`, but the expression is still evaluated
                // at runtime and must contribute its send sites and type
                // effects to the final pass.
                let _ = self.eval_node(&superclass, environment);
            }
            if let Some(body) = class.body() {
                let mut class_environment = environment.clone();
                class_environment.self_type = Self::class_object_type(&class_name);
                let class_body_key = MethodKey {
                    owner: Some(class_name),
                    name: "<class-body>".to_owned(),
                    singleton: true,
                };
                class_environment.method_key = Some(class_body_key.clone());
                let previous_substitution_context =
                    self.substitution_context.replace(class_body_key);
                self.eval_node(&body, &mut class_environment);
                self.substitution_context = previous_substitution_context;
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(module) = node.as_module_node() {
            if self.seed_calls || self.is_rbi_definition(node) {
                return Eval::value(Type::Nil);
            }
            let module_name = self.scoped_constant_name(
                environment,
                &self
                    .constant_reference_name(&module.constant_path())
                    .unwrap_or_else(|| prism::text(self.program.source, &module.constant_path())),
            );
            if let Some(body) = module.body() {
                let mut module_environment = environment.clone();
                module_environment.self_type = Self::class_object_type(&module_name);
                let module_body_key = MethodKey {
                    owner: Some(module_name),
                    name: "<module-body>".to_owned(),
                    singleton: true,
                };
                module_environment.method_key = Some(module_body_key.clone());
                let previous_substitution_context =
                    self.substitution_context.replace(module_body_key);
                self.eval_node(&body, &mut module_environment);
                self.substitution_context = previous_substitution_context;
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(singleton) = node.as_singleton_class_node() {
            if self.seed_calls || self.is_rbi_definition(node) {
                return Eval::value(Type::Nil);
            }
            let expression = singleton.expression();
            let expression_type = self.eval_node(&expression, environment).type_;
            let owner = match &expression_type {
                Type::Named(owner, arguments) if name_matches(owner, "Class") => arguments
                    .first()
                    .and_then(Self::named_type_name)
                    .or_else(|| self.constant_reference_name(&expression)),
                Type::Named(owner, _) => Some(owner.clone()),
                _ => self.constant_reference_name(&expression),
            };
            if let Some(body) = singleton.body() {
                let mut singleton_environment = environment.clone();
                singleton_environment.self_type = expression_type;
                let singleton_body_key = MethodKey {
                    owner,
                    name: "<singleton-body>".to_owned(),
                    singleton: true,
                };
                singleton_environment.method_key = Some(singleton_body_key.clone());
                let previous_substitution_context =
                    self.substitution_context.replace(singleton_body_key);
                self.eval_node(&body, &mut singleton_environment);
                self.substitution_context = previous_substitution_context;
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if self.config.enable_cfg {
            if let Some(result) = self.eval_cfg_value_dispatch(node, environment) {
                return result;
            }
        }
        if let Some((target, value, operator)) = self.hir_assignment_for_node(node) {
            if self.config.enable_cfg && self.has_cfg_assignment_operation(node) {
                return self.transfer_cfg_assignment(node, target, value, operator, environment);
            }
            if self.config.enable_cfg {
                self.record_cfg_fallback(node, "assignment", CfgFallbackKind::UnsupportedOperation);
            }
            return self.eval_hir_assignment(node, target, value, operator, environment);
        }
        if let Some(call) = node.as_call_node() {
            let hir_call = self.hir_call_view(node, call).unwrap_or_else(|| {
                let (start, end) = prism::span(node);
                    panic!(
                        "every ordinary call must have an owned HIR call shape: {}..{} `{}` (HIR expressions: {}, calls: {})",
                        start,
                        end,
                        String::from_utf8_lossy(self.program.source.get(start..end).unwrap_or_default()),
                        self.program.hir_program.expressions.len(),
                        self.program.hir_call_ids.len()
                    )
            });
            return self.eval_call_result(node, &hir_call, environment);
        }
        if let Some(multi) = node.as_multi_write_node() {
            let previous_expected_return = self.expected_return_type.take();
            let previous_preserve_literal_tuples = self.preserve_literal_tuples;
            self.preserve_literal_tuples = true;
            if let Some(array) = multi.value().as_array_node() {
                self.expected_return_type =
                    Some(Type::Tuple(vec![Type::Any; array.elements().len()]));
            }
            let mut result = self.eval_node(&multi.value(), environment);
            self.expected_return_type = previous_expected_return;
            self.preserve_literal_tuples = previous_preserve_literal_tuples;
            if let Some(type_) = result.normal_type.clone() {
                let lefts = multi.lefts().into_iter().collect::<Vec<_>>();
                let rights = multi.rights().into_iter().collect::<Vec<_>>();
                let known_length = multi
                    .value()
                    .as_array_node()
                    .filter(|array| {
                        array
                            .elements()
                            .iter()
                            .all(|element| element.as_splat_node().is_none())
                    })
                    .map(|array| array.elements().len());
                for (index, target) in lefts.iter().enumerate() {
                    self.bind_for_target(
                        target,
                        self.multi_assignment_element_type(&type_, index, known_length),
                        environment,
                    );
                }
                if let Some(rest) = multi.rest() {
                    self.bind_for_target(
                        &rest,
                        Type::union([
                            Type::Nil,
                            Type::Array(Box::new(self.array_element_type(&type_))),
                        ]),
                        environment,
                    );
                }
                let right_start = known_length
                    .map(|length| lefts.len().max(length.saturating_sub(rights.len())))
                    .unwrap_or(0);
                for (index, target) in rights.iter().enumerate() {
                    self.bind_for_target(
                        target,
                        self.multi_assignment_element_type(
                            &type_,
                            right_start + index,
                            known_length,
                        ),
                        environment,
                    );
                }
            }
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(read) = node.as_class_variable_read_node() {
            let actual = self.class_var_type(environment, &prism::constant_name(read.name()));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_global_variable_read_node() {
            let name = prism::constant_name(read.name());
            self.record_shared_read(SharedKey::Global(name.clone()), environment);
            let actual = self.globals.get(&name).cloned().unwrap_or(Type::Any);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_instance_variable_read_node() {
            let name = prism::constant_name(read.name());
            let actual = self.ivar_type(environment, &name);
            let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_local_variable_read_node() {
            let actual = environment.get(&prism::constant_name(read.name()));
            let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
            return Eval::value(self.record(node, type_));
        }
        if node.as_it_local_variable_read_node().is_some() {
            let type_ = self.apply_inline_assertion(node, environment.get("it"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(numbered) = node.as_numbered_reference_read_node() {
            let type_ = self
                .apply_inline_assertion(node, environment.get(&format!("_{}", numbered.number())));
            return Eval::value(self.record(node, type_));
        }
        if let Some(constant) = node.as_constant_read_node() {
            let name = prism::constant_name(constant.name());
            let actual = self.constant_type(environment, &name);
            self.report_missing_constant_if_needed(node, environment, &name);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(path) = node.as_constant_path_node() {
            let name = self.constant_path_name(&path);
            let actual = self.constant_type(environment, &name);
            self.report_missing_constant_if_needed(node, environment, &name);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if node.as_self_node().is_some() {
            let type_ = self.apply_inline_assertion(node, environment.self_type.clone());
            return Eval::value(self.record(node, type_));
        }
        if let Some(defined) = node.as_defined_node() {
            // Sorbet inspects the operand of `defined?` for send accounting
            // and type propagation, but it does not report ordinary missing
            // API errors from that operand: the expression is only queried
            // for whether it could be defined at runtime.
            let previous_suppression = self.reporting.suppress_diagnostics;
            self.reporting.suppress_diagnostics = true;
            let _ = self.eval_node(&defined.value(), environment);
            self.reporting.suppress_diagnostics = previous_suppression;
            let type_ = self.apply_inline_assertion(node, Type::union([Type::Nil, Type::String]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(range) = node.as_range_node() {
            let left_type = range
                .left()
                .map_or(Type::Nil, |left| self.eval_node(&left, environment).type_);
            let right_type = range
                .right()
                .map_or(Type::Nil, |right| self.eval_node(&right, environment).type_);
            let type_ = self.apply_inline_assertion(
                node,
                Type::Named("Range".to_owned(), vec![left_type, right_type]),
            );
            return Eval::value(self.record(node, type_));
        }
        if node.as_regular_expression_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::named("Regexp"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(regexp) = node.as_interpolated_regular_expression_node() {
            for part in &regexp.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::named("Regexp"));
            return Eval::value(self.record(node, type_));
        }
        if node.as_source_file_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if node.as_source_line_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Integer);
            return Eval::value(self.record(node, type_));
        }
        if node.as_source_encoding_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::named("Encoding"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(flip_flop) = node.as_flip_flop_node() {
            if let Some(left) = flip_flop.left() {
                self.eval_node(&left, environment);
            }
            if let Some(right) = flip_flop.right() {
                self.eval_node(&right, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::bool());
            return Eval::value(self.record(node, type_));
        }
        if node.as_match_last_line_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::union([Type::Nil, Type::Integer]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(match_last_line) = node.as_interpolated_match_last_line_node() {
            for part in &match_last_line.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::union([Type::Nil, Type::Integer]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(imaginary) = node.as_imaginary_node() {
            self.eval_node(&imaginary.numeric(), environment);
            let type_ = self.apply_inline_assertion(node, Type::named("Complex"));
            return Eval::value(self.record(node, type_));
        }
        if node.as_rational_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::named("Rational"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(symbol) = node.as_interpolated_symbol_node() {
            for part in &symbol.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::Symbol);
            return Eval::value(self.record(node, type_));
        }
        if node.as_x_string_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(xstring) = node.as_interpolated_x_string_node() {
            for part in &xstring.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(integer) = node.as_integer_node() {
            let _ = integer.value();
            let type_ = self.apply_inline_assertion(node, Type::Integer);
            return Eval::value(self.record(node, type_));
        }
        if node.as_float_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Float);
            return Eval::value(self.record(node, type_));
        }
        if node.as_string_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(string) = node.as_interpolated_string_node() {
            for part in &string.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(embedded) = node.as_embedded_statements_node() {
            if let Some(statements) = embedded.statements() {
                return self.eval_node(&statements.as_node(), environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(embedded) = node.as_embedded_variable_node() {
            return self.eval_node(&embedded.variable(), environment);
        }
        if node.as_symbol_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Symbol);
            return Eval::value(self.record(node, type_));
        }
        if node.as_nil_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Nil);
            return Eval::value(self.record(node, type_));
        }
        if node.as_true_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::True);
            return Eval::value(self.record(node, type_));
        }
        if node.as_false_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::False);
            return Eval::value(self.record(node, type_));
        }
        if let Some(lambda) = node.as_lambda_node() {
            let signature = MethodState::inferred(lambda.parameters().and_then(|parameters| {
                parameters
                    .as_block_parameters_node()
                    .and_then(|parameters| parameters.parameters())
                    .or_else(|| parameters.as_parameters_node())
            }))
            .body_signature();
            let parameters = lambda.parameters().and_then(|parameters| {
                parameters
                    .as_block_parameters_node()
                    .and_then(|parameters| parameters.parameters())
                    .or_else(|| parameters.as_parameters_node())
            });
            let mut closure_environment = environment.clone();
            self.bind_parameters(parameters, Some(&signature), &mut closure_environment, true);
            let body_result = lambda
                .body()
                .map(|body| self.eval_node(&body, &mut closure_environment))
                .unwrap_or_else(|| Eval::value(Type::Nil));
            let return_type = body_result.method_return_type();
            let type_ = self.apply_inline_assertion_in_environment(
                node,
                Type::Proc(signature.params, Box::new(return_type)),
                environment,
            );
            return Eval::value(self.record(node, type_));
        }
        if let Some(array) = node.as_array_node() {
            let tuple_depth = self.literal_tuple_depth;
            self.literal_tuple_depth += 1;
            let mut element_types = Vec::new();
            let mut fixed_length = true;
            let mut element = Type::Never;
            for child in &array.elements() {
                let child_type = self.eval_node(&child, environment).type_;
                let child_type = if child.as_splat_node().is_some() {
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
                // An empty nested array inside a multi-assignment tuple is
                // a bottom-valued container, not an independently untyped
                // array.  Keeping `Never` here lets a concrete sibling
                // branch refine it during tuple joins without losing the
                // tuple's known component types.
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
            let type_ = self.apply_inline_assertion_in_environment(node, inferred, environment);
            return Eval::value(self.record(node, type_));
        }
        if let Some(hash) = node.as_hash_node() {
            let mut key = Type::Never;
            let mut value = Type::Never;
            for child in &hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    let key_type = self.eval_node(&assoc.key(), environment).type_;
                    let value_type = self.eval_node(&assoc.value(), environment).type_;
                    key = key.join(&key_type);
                    value = value.join(&value_type);
                } else if let Some(splat) = child.as_assoc_splat_node() {
                    if let Some(expression) = splat.value() {
                        match self.eval_node(&expression, environment).type_ {
                            Type::Hash(splat_key, splat_value) => {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                            }
                            Type::Any => {
                                key = Type::Any;
                                value = Type::Any;
                            }
                            _ => {}
                        }
                    }
                } else {
                    self.eval_node(&child, environment);
                }
            }
            let key = if key.is_never() { Type::Any } else { key };
            let value = if value.is_never() { Type::Any } else { value };
            let type_ = self.apply_inline_assertion_in_environment(
                node,
                Type::Hash(Box::new(key), Box::new(value)),
                environment,
            );
            return Eval::value(self.record(node, type_));
        }
        if let Some(keyword_hash) = node.as_keyword_hash_node() {
            let mut key = Type::Never;
            let mut value = Type::Never;
            for child in &keyword_hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    key = key.join(&self.eval_node(&assoc.key(), environment).type_);
                    value = value.join(&self.eval_node(&assoc.value(), environment).type_);
                } else if let Some(splat) = child.as_assoc_splat_node() {
                    if let Some(expression) = splat.value() {
                        match self.eval_node(&expression, environment).type_ {
                            Type::Hash(splat_key, splat_value) => {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                            }
                            Type::Any => {
                                key = Type::Any;
                                value = Type::Any;
                            }
                            _ => {}
                        }
                    }
                }
            }
            let key = if key.is_never() { Type::Any } else { key };
            let value = if value.is_never() { Type::Any } else { value };
            let type_ = self.apply_inline_assertion_in_environment(
                node,
                Type::Hash(Box::new(key), Box::new(value)),
                environment,
            );
            return Eval::value(self.record(node, type_));
        }
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                let result = self.eval_node(&body, environment);
                let type_ = self.apply_inline_assertion_in_environment(
                    node,
                    result.type_.clone(),
                    environment,
                );
                return Eval {
                    type_: self.record(node, type_),
                    ..result
                };
            }
            let type_ = self.apply_inline_assertion_in_environment(node, Type::Nil, environment);
            return Eval::value(self.record(node, type_));
        }
        if let Some(begin) = node.as_begin_node() {
            return self.eval_begin(node, &begin, environment);
        }
        if let Some(rescue) = node.as_rescue_modifier_node() {
            return self.eval_rescue_modifier(node, &rescue, environment);
        }
        if let Some(if_node) = node.as_if_node() {
            return self.eval_if(node, &if_node, environment);
        }
        if let Some(unless) = node.as_unless_node() {
            return self.eval_unless(node, &unless, environment);
        }
        if let Some(case_node) = node.as_case_node() {
            return self.eval_case(node, &case_node, environment);
        }
        if let Some(case_match) = node.as_case_match_node() {
            return self.eval_case_match(node, &case_match, environment);
        }
        if let Some(and) = node.as_and_node() {
            let left_node = and.left();
            let left = self.eval_node(&left_node, environment).type_;
            let mut right_environment = environment.clone();
            self.narrow_from_predicate(&left_node, &mut right_environment, true);
            let right_node = and.right();
            let right = self.eval_node(&right_node, &mut right_environment).type_;
            let type_ = self.apply_inline_assertion(node, Type::union([left.falsy_part(), right]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(or) = node.as_or_node() {
            let left_node = or.left();
            let left = self.eval_node(&left_node, environment).type_;
            let mut right_environment = environment.clone();
            self.narrow_from_predicate(&left_node, &mut right_environment, false);
            let right_node = or.right();
            let right = self.eval_node(&right_node, &mut right_environment).type_;
            let type_ = self.apply_inline_assertion(node, Type::union([left.truthy_part(), right]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(return_node) = node.as_return_node() {
            let type_ = self.eval_control_arguments(return_node.arguments(), environment);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::returned(self.record(node, type_));
        }
        if let Some(break_node) = node.as_break_node() {
            let type_ = self.eval_control_arguments(break_node.arguments(), environment);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::broken(self.record(node, type_));
        }
        if let Some(next_node) = node.as_next_node() {
            let type_ = self.eval_control_arguments(next_node.arguments(), environment);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::continued(self.record(node, type_));
        }
        if let Some(yield_node) = node.as_yield_node() {
            let hir_call = self
                .hir_call_for_node(node)
                .expect("every yield must have an owned HIR call shape");
            let argument_inputs =
                hir_call_argument_inputs(&hir_call.arguments, yield_node.arguments());
            let evaluated = self.evaluate_call_arguments(argument_inputs, environment);
            let arguments = evaluated.arguments;
            let argument_types = arguments.argument_types.clone();
            let method_key = environment.method_key.clone();
            let expected_block_parameters = method_key
                .as_ref()
                .and_then(|key| self.declarations.methods.get(key))
                .and_then(|state| state.block.as_ref())
                .and_then(|block| proc_parts(block).map(|(parameters, _)| parameters.to_vec()));
            if let Some(expected) = expected_block_parameters {
                for (index, actual) in argument_types.iter().enumerate() {
                    if let Some(expected) = expected.get(index) {
                        if matches!(expected, Type::Named(name, _) if name.starts_with('{'))
                            && matches!(actual, Type::Hash(_, _))
                        {
                            continue;
                        }
                        if !self.is_assignable(actual, expected) {
                            if let Some(argument) = arguments.argument_nodes.get(index) {
                                let actual_description =
                                    self.argument_type_description(argument, actual);
                                self.error(
                                    argument,
                                    format!(
                                        "Expected `{expected}` but found `{actual_description}` for argument `arg{index}`"
                                    ),
                                );
                            }
                        }
                    }
                }
            }
            if let Some(key) = method_key.as_ref() {
                if let Some(state) = self.declarations.methods.get_mut(key) {
                    if state.observe_yield_arguments(&argument_types) {
                        self.fixpoint.changed_methods.insert(key.clone());
                    }
                }
            }
            let block_return_type = method_key
                .as_ref()
                .and_then(|key| self.declarations.methods.get(key))
                .and_then(|state| state.block_return_type.clone())
                .unwrap_or(Type::Any);
            let normal_type = evaluated.all_normal.then_some(block_return_type);
            let flow = evaluated.abrupt_flow.union(
                normal_type
                    .as_ref()
                    .map_or(Flow::empty(), |_| Flow::normal()),
            );
            let mut result = Eval::from_parts(normal_type, evaluated.abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if node.as_retry_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Never);
            return Eval::retried(self.record(node, type_));
        }
        if let Some(super_node) = node.as_super_node() {
            let block = super_node.block();
            let hir_call = self
                .hir_call_for_node(node)
                .cloned()
                .expect("every super call must have an owned HIR call shape");
            let actual = self.eval_super(
                node,
                Some(&hir_call),
                super_node.arguments(),
                None,
                block.as_ref(),
                environment,
            );
            let type_ = self.apply_inline_assertion(node, actual);
            let type_ = self.record(node, type_);
            if self.super_terminates(environment) {
                return Eval::raised(type_);
            } else {
                return Eval::value(type_);
            }
        }
        if let Some(super_node) = node.as_forwarding_super_node() {
            let block = super_node.block().map(|block| block.as_node());
            let hir_call = self
                .hir_call_for_node(node)
                .cloned()
                .expect("every forwarding super call must have an owned HIR call shape");
            let actual = self.eval_super(
                node,
                Some(&hir_call),
                None,
                Some(&super_node),
                block.as_ref(),
                environment,
            );
            let type_ = self.apply_inline_assertion(node, actual);
            let type_ = self.record(node, type_);
            if self.super_terminates(environment) {
                return Eval::raised(type_);
            } else {
                return Eval::value(type_);
            }
        }
        if let Some(block) = node.as_block_node() {
            let block_type = self.eval_block(&block, &[], environment).type_;
            let type_ = self.apply_inline_assertion_in_environment(node, block_type, environment);
            let type_ = self.apply_inline_assertion_in_environment(node, type_, environment);
            return Eval::value(self.record(node, type_));
        }
        if let Some(splat) = node.as_splat_node() {
            let type_ = splat
                .expression()
                .map_or(Type::Any, |value| self.eval_node(&value, environment).type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(while_node) = node.as_while_node() {
            let predicate = while_node.predicate();
            let statements = while_node.statements();
            let mut result = self.eval_loop(&predicate, statements.as_ref(), environment, true);
            let type_ =
                self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(until_node) = node.as_until_node() {
            let predicate = until_node.predicate();
            let statements = until_node.statements();
            let mut result = self.eval_loop(&predicate, statements.as_ref(), environment, false);
            let type_ =
                self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(for_node) = node.as_for_node() {
            return self.eval_for(node, &for_node, environment);
        }

        let type_ = self.apply_inline_assertion_in_environment(node, Type::Any, environment);
        Eval::value(self.record(node, type_))
    }
}
