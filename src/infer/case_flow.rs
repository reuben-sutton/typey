//! Parser-backed `case` and pattern flow retained by the legacy evaluator.
//!
//! Owned HIR case transfer lives in `cfg_transfer/patterns.rs`; this module
//! contains the compatibility path for Prism case and case-match nodes.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_case<'node>(
        &mut self,
        node: &Node<'node>,
        case_node: &ruby_prism::CaseNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = case_node.predicate();
        let predicate_type = predicate
            .as_ref()
            .map(|predicate| self.eval_node(predicate, environment).type_);
        let base = environment.clone();
        let mut branch_environment: Option<Environment> = None;
        let mut result: Option<Eval> = None;
        let mut covered_type = Type::Never;
        let mut terminating_type = Type::Never;
        let mut all_conditions_are_type_tests = true;

        for condition in &case_node.conditions() {
            let Some(when_node) = condition.as_when_node() else {
                continue;
            };
            let conditions = when_node.conditions().into_iter().collect::<Vec<_>>();
            let mut when_environment = base.clone();
            let mut condition_type = Type::Never;
            let mut condition_is_type_test = true;
            for value in &conditions {
                let value_type = self.eval_node(&value, &mut when_environment).type_;
                let is_type_test = Self::is_case_type_test(&value, &value_type);
                all_conditions_are_type_tests &= is_type_test;
                condition_is_type_test &= is_type_test;
                let value_type = Self::class_object_value_type(&value_type).unwrap_or(value_type);
                condition_type = condition_type.join(&value_type);
            }
            covered_type = covered_type.join(&condition_type);
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target(predicate, &mut when_environment, &condition_type);
                self.narrow_discriminated_case_target(
                    predicate,
                    &conditions,
                    &mut when_environment,
                );
            }
            let when_result = if let Some(statements) = when_node.statements() {
                self.eval_statements(&statements, &mut when_environment)
            } else {
                Eval::value(Type::Nil)
            };
            if condition_is_type_test && !when_result.flow.contains(FlowKind::Normal) {
                terminating_type = terminating_type.join(&condition_type);
            }
            let previous_flow = result
                .as_ref()
                .map_or_else(Flow::empty, |result| result.flow);
            let when_flow = when_result.flow;
            result = Some(match result {
                Some(current) => Eval::combine(&current, &when_result),
                None => when_result,
            });
            branch_environment = Some(match branch_environment {
                Some(current) => self.join_flow_environments(
                    &current,
                    previous_flow,
                    &when_environment,
                    when_flow,
                ),
                None => when_environment,
            });
        }

        let mut else_environment = base.clone();
        if !terminating_type.is_never() {
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target_excluding(
                    predicate,
                    &mut else_environment,
                    &terminating_type,
                );
            }
        }
        let else_result = if let Some(else_clause) = case_node.else_clause() {
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target_without(
                    predicate,
                    &mut else_environment,
                    &covered_type,
                    all_conditions_are_type_tests,
                );
            }
            if let Some(statements) = else_clause.statements() {
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            // The unmatched path remains possible unless the predicate's
            // finite union is covered by the `when` conditions. Preserve its
            // narrowed environment for statements after the case, while
            // avoiding a spurious nil value for exhaustive class switches.
            let unmatched = predicate_type.as_ref().map(|candidate| {
                self.case_unmatched_type(candidate, &covered_type, all_conditions_are_type_tests)
            });
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target_without(
                    predicate,
                    &mut else_environment,
                    &covered_type,
                    all_conditions_are_type_tests,
                );
            }
            if unmatched.as_ref().is_some_and(Type::is_never) {
                Eval::from_parts(None, OutcomeTypes::default(), Flow::empty())
            } else {
                Eval::value(Type::Nil)
            }
        };
        let previous_flow = result
            .as_ref()
            .map_or_else(Flow::empty, |result| result.flow);
        let else_flow = else_result.flow;
        result = Some(match result {
            Some(current) => Eval::combine(&current, &else_result),
            None => else_result,
        });
        branch_environment = Some(match branch_environment {
            Some(current) => {
                self.join_flow_environments(&current, previous_flow, &else_environment, else_flow)
            }
            None => else_environment,
        });
        *environment = branch_environment.expect("case always has an implicit else path");
        let mut result = result.expect("case always has an implicit else path");
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn narrow_case_target<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        condition_type: &Type,
    ) {
        if let Some(name) = Self::case_target_name(predicate) {
            let current = environment.get(&name);
            environment.bind(name, self.meet_predicate_type(&current, condition_type));
        }
    }

    fn narrow_discriminated_case_target<'node>(
        &self,
        predicate: &Node<'node>,
        conditions: &[Node<'node>],
        environment: &mut Environment,
    ) {
        let Some(call) = predicate.as_call_node() else {
            return;
        };
        if prism::constant_name(call.name()) != "type" {
            return;
        }
        let Some(receiver) = call.receiver() else {
            return;
        };
        let Some(local) = receiver.as_local_variable_read_node() else {
            return;
        };
        let local_name = prism::constant_name(local.name());
        let current = environment.get(&local_name);
        let Some(current_name) = Self::named_type_name(&current) else {
            return;
        };
        let symbols = conditions
            .iter()
            .filter_map(|condition| {
                condition
                    .as_symbol_node()
                    .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
            })
            .collect::<BTreeSet<_>>();
        if symbols.is_empty() {
            return;
        }
        let narrowed = self
            .fixpoint
            .symbol_method_returns
            .iter()
            .filter_map(|(key, symbol)| {
                (key.name == "type"
                    && !key.singleton
                    && symbols.contains(symbol)
                    && key
                        .owner
                        .as_deref()
                        .is_some_and(|owner| self.nominal_subtype(owner, &current_name)))
                .then(|| Type::named(key.owner.as_ref().expect("owner checked").clone()))
            })
            .collect::<Vec<_>>();
        if !narrowed.is_empty() {
            environment.bind(local_name, Type::union(narrowed));
        }
    }

    fn narrow_case_target_without<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        excluded: &Type,
        all_conditions_are_type_tests: bool,
    ) {
        if let Some(name) = Self::case_target_name(predicate) {
            let current = environment.get(&name);
            environment.bind(
                name,
                self.case_unmatched_type(&current, excluded, all_conditions_are_type_tests),
            );
        }
    }

    fn narrow_case_target_excluding<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        excluded: &Type,
    ) {
        if let Some(name) = Self::case_target_name(predicate) {
            let current = environment.get(&name);
            environment.bind(name, current.without(excluded));
        }
    }

    fn case_target_name(node: &Node<'_>) -> Option<String> {
        if let Some(parentheses) = node.as_parentheses_node() {
            return parentheses
                .body()
                .and_then(|body| Self::case_target_name(&body));
        }
        if let Some(statements) = node.as_statements_node() {
            return statements
                .body()
                .into_iter()
                .last()
                .and_then(|body| Self::case_target_name(&body));
        }
        node.as_local_variable_read_node()
            .map(|local| prism::constant_name(local.name()))
            .or_else(|| {
                node.as_local_variable_write_node()
                    .map(|write| prism::constant_name(write.name()))
            })
    }

    fn is_case_type_test(node: &Node<'_>, value_type: &Type) -> bool {
        Self::class_object_instance_type(value_type).is_some()
            || node.as_constant_read_node().is_some_and(|constant| {
                matches!(
                    prism::constant_name(constant.name()).as_str(),
                    "Array"
                        | "BasicObject"
                        | "Class"
                        | "Complex"
                        | "FalseClass"
                        | "Float"
                        | "Hash"
                        | "Integer"
                        | "NilClass"
                        | "Numeric"
                        | "Object"
                        | "Rational"
                        | "Regexp"
                        | "String"
                        | "Symbol"
                        | "TrueClass"
                )
            })
            || node.as_true_node().is_some()
            || node.as_false_node().is_some()
            || node.as_nil_node().is_some()
    }

    fn case_unmatched_type(
        &self,
        candidate: &Type,
        covered: &Type,
        all_conditions_are_type_tests: bool,
    ) -> Type {
        if !all_conditions_are_type_tests {
            return candidate.clone();
        }
        match candidate {
            Type::Any => Type::Any,
            Type::Union(members) => Type::union(members.iter().filter_map(|member| {
                (!self.is_assignable(member, covered)).then_some(member.clone())
            })),
            candidate if self.is_assignable(candidate, covered) => Type::Never,
            candidate => candidate.clone(),
        }
    }

    pub(super) fn eval_case_match<'node>(
        &mut self,
        node: &Node<'node>,
        case_node: &ruby_prism::CaseMatchNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = case_node.predicate();
        if let Some(predicate) = predicate.as_ref() {
            self.eval_node(predicate, environment);
        }
        let base = environment.clone();
        let candidate = predicate
            .as_ref()
            .map_or(Type::Any, |predicate| self.node_type(predicate, &base));
        let mut branch_environment: Option<Environment> = None;
        let mut result: Option<Eval> = None;

        for condition in &case_node.conditions() {
            let Some(in_node) = condition.as_in_node() else {
                continue;
            };
            let mut in_environment = base.clone();
            let constraint = self.bind_pattern(&in_node.pattern(), &candidate, &mut in_environment);
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target(predicate, &mut in_environment, &constraint);
            }
            let in_result = if let Some(statements) = in_node.statements() {
                self.eval_statements(&statements, &mut in_environment)
            } else {
                Eval::value(Type::Nil)
            };
            let previous_flow = result
                .as_ref()
                .map_or_else(Flow::empty, |result| result.flow);
            let in_flow = in_result.flow;
            result = Some(match result {
                Some(current) => Eval::combine(&current, &in_result),
                None => in_result,
            });
            branch_environment = Some(match branch_environment {
                Some(current) => {
                    self.join_flow_environments(&current, previous_flow, &in_environment, in_flow)
                }
                None => in_environment,
            });
        }

        let mut else_environment = base;
        let else_result = if let Some(else_clause) = case_node.else_clause() {
            if let Some(statements) = else_clause.statements() {
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            Eval::value(Type::Nil)
        };
        let previous_flow = result
            .as_ref()
            .map_or_else(Flow::empty, |result| result.flow);
        let else_flow = else_result.flow;
        result = Some(match result {
            Some(current) => Eval::combine(&current, &else_result),
            None => else_result,
        });
        branch_environment = Some(match branch_environment {
            Some(current) => {
                self.join_flow_environments(&current, previous_flow, &else_environment, else_flow)
            }
            None => else_environment,
        });
        *environment = branch_environment.expect("pattern match always has an else path");
        let mut result = result.expect("pattern match always has an else path");
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }
}
