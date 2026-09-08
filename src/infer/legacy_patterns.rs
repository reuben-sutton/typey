//! Pattern binding and constraint inference for the recursive Prism evaluator.

use super::{Analyzer, Environment};
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;

impl<'src> Analyzer<'src> {
    pub(super) fn node_type<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Type {
        let mut environment = environment.clone();
        self.eval_node(node, &mut environment).type_
    }

    pub(super) fn bind_pattern<'node>(
        &mut self,
        pattern: &Node<'node>,
        candidate: &Type,
        environment: &mut Environment,
    ) -> Type {
        if let Some(capture) = pattern.as_capture_pattern_node() {
            let constraint = self.pattern_constraint(&capture.value(), candidate, environment);
            let narrowed = if constraint.is_any() {
                candidate.clone()
            } else {
                candidate.meet(&constraint)
            };
            environment.bind(
                prism::constant_name(capture.target().name()),
                narrowed.clone(),
            );
            return if narrowed.is_never() {
                constraint
            } else {
                narrowed
            };
        }
        if let Some(target) = pattern.as_local_variable_target_node() {
            environment.bind(prism::constant_name(target.name()), candidate.clone());
            return Type::Any;
        }
        if let Some(array) = pattern.as_array_pattern_node() {
            let element = self.array_element_type(candidate);
            let mut constraint = Type::Never;
            for child in &array.requireds() {
                constraint = constraint.join(&self.bind_pattern(&child, &element, environment));
            }
            if let Some(rest) = array.rest() {
                let rest_type = Type::Array(Box::new(element.clone()));
                constraint = constraint.join(&self.bind_pattern(&rest, &rest_type, environment));
            }
            for child in &array.posts() {
                constraint = constraint.join(&self.bind_pattern(&child, &element, environment));
            }
            let element_constraint = if constraint.is_never() {
                Type::Any
            } else {
                constraint
            };
            return Type::Array(Box::new(element_constraint));
        }
        if let Some(hash) = pattern.as_hash_pattern_node() {
            let value = match candidate {
                Type::Hash(_, value) => value.as_ref().clone(),
                _ => Type::Any,
            };
            let mut value_constraint = Type::Never;
            for child in &hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    value_constraint = value_constraint.join(&self.bind_pattern(
                        &assoc.value(),
                        &value,
                        environment,
                    ));
                }
            }
            let value_constraint = if value_constraint.is_never() {
                Type::Any
            } else {
                value_constraint
            };
            return Type::Hash(Box::new(Type::Any), Box::new(value_constraint));
        }
        if let Some(alternation) = pattern.as_alternation_pattern_node() {
            let left = self.pattern_constraint(&alternation.left(), candidate, environment);
            let right = self.pattern_constraint(&alternation.right(), candidate, environment);
            return left.join(&right);
        }
        self.pattern_constraint(pattern, candidate, environment)
    }

    pub(super) fn pattern_constraint<'node>(
        &mut self,
        pattern: &Node<'node>,
        candidate: &Type,
        environment: &mut Environment,
    ) -> Type {
        if pattern.as_local_variable_target_node().is_some()
            || pattern.as_implicit_node().is_some()
            || pattern.as_implicit_rest_node().is_some()
        {
            return Type::Any;
        }
        if let Some(capture) = pattern.as_capture_pattern_node() {
            return self.pattern_constraint(&capture.value(), candidate, environment);
        }
        if let Some(array) = pattern.as_array_pattern_node() {
            let element = self.array_element_type(candidate);
            let mut element_constraint = Type::Never;
            for child in &array.requireds() {
                element_constraint = element_constraint.join(&self.pattern_constraint(
                    &child,
                    &element,
                    environment,
                ));
            }
            for child in &array.posts() {
                element_constraint = element_constraint.join(&self.pattern_constraint(
                    &child,
                    &element,
                    environment,
                ));
            }
            return Type::Array(Box::new(if element_constraint.is_never() {
                Type::Any
            } else {
                element_constraint
            }));
        }
        if let Some(alternation) = pattern.as_alternation_pattern_node() {
            return self
                .pattern_constraint(&alternation.left(), candidate, environment)
                .join(&self.pattern_constraint(&alternation.right(), candidate, environment));
        }
        let type_ = self.node_type(pattern, environment);
        Self::class_object_value_type(&type_).unwrap_or(type_)
    }
}
