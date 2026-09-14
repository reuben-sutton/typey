//! Small receiver-independent dispatch helpers shared by owned transfer.
//!
//! Call execution itself lives in `cfg_transfer`. This module only contains
//! contracts that are useful after a receiver has already been represented as
//! a `Type`; it intentionally has no parser-backed evaluator.

use super::{name_matches, AccessorKind, Analyzer, Environment, MethodKey};
use crate::signature::{self, MethodSig};
use crate::types::Type;

impl<'src> Analyzer<'src> {
    pub(super) fn private_call_allowed(&self, key: &MethodKey, environment: &Environment) -> bool {
        let Some(current) = environment.method_key.as_ref() else {
            return false;
        };
        let Some(current_owner) = current.owner.as_deref() else {
            return false;
        };
        let Some(resolved_owner) = self
            .resolve_method_key(key)
            .and_then(|resolved| resolved.owner)
        else {
            return false;
        };
        current_owner == resolved_owner
            || (!current.singleton && self.nominal_subtype(current_owner, &resolved_owner))
            || (current.singleton
                && key.singleton
                && self.nominal_subtype(current_owner, &resolved_owner))
    }

    pub(super) fn common_method_helper_shadowed(
        &self,
        receiver: &Type,
        name: &str,
        environment: &Environment,
    ) -> bool {
        matches!(name, "method" | "public_method" | "singleton_method")
            && Self::class_object_instance_type(receiver).is_some()
            && self
                .receiver_method_key(None, receiver, name, environment)
                .and_then(|key| self.resolve_method_key(&key))
                .is_some()
    }

    pub(super) fn dynamic_splat_element_type(type_: &Type) -> Option<Type> {
        match type_ {
            Type::Array(element) => Some(element.as_ref().clone()),
            Type::Nil => Some(Type::Never),
            Type::Union(members) => {
                let mut element = Type::Never;
                for member in members {
                    element = element.join(&Self::dynamic_splat_element_type(member)?);
                }
                Some(element)
            }
            Type::Any | Type::Anything => None,
            other => Some(other.clone()),
        }
    }

    pub(super) fn array_coercion_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => element.as_ref().clone(),
            Type::Tuple(elements) => elements
                .iter()
                .fold(Type::Never, |current, element| current.join(element)),
            Type::Union(members) => members
                .iter()
                .filter(|member| !matches!(member, Type::Nil))
                .map(|member| self.array_coercion_element_type(member))
                .fold(Type::Never, |current, element| current.join(&element)),
            Type::Nil => Type::Never,
            other => other.clone(),
        }
    }

    pub(super) fn eval_accessor_call(
        &mut self,
        key: &MethodKey,
        kind: AccessorKind,
        argument_types: &[Type],
        environment: &Environment,
    ) -> Type {
        let Some(owner) = key.owner.as_deref() else {
            return Type::Any;
        };
        let name = key.name.strip_suffix('=').unwrap_or(&key.name);
        match kind {
            AccessorKind::Reader => self
                .struct_field_type(owner, name, environment)
                .or_else(|| {
                    self.inferred_accessor_ivar_type(owner, name, key.singleton, environment)
                })
                .unwrap_or(Type::Any),
            AccessorKind::Writer => {
                let type_ = argument_types.first().cloned().unwrap_or(Type::Any);
                self.observe_accessor_ivar(owner, name, key.singleton, &type_);
                type_
            }
        }
    }

    pub(super) fn eval_node_helpers_method(
        &self,
        receiver: &Type,
        name: &str,
        argument_types: &[Type],
    ) -> Option<Type> {
        if name == "class" {
            return Some(match receiver {
                Type::Any | Type::Anything => Type::Any,
                Type::Never => Type::Never,
                Type::True => Self::class_object_type("TrueClass"),
                Type::False => Self::class_object_type("FalseClass"),
                Type::Nil => Self::class_object_type("NilClass"),
                Type::Integer => Self::class_object_type("Integer"),
                Type::Float => Self::class_object_type("Float"),
                Type::String => Self::class_object_type("String"),
                Type::Symbol => Self::class_object_type("Symbol"),
                Type::Array(_) | Type::Tuple(_) => Self::class_object_type("Array"),
                Type::Hash(_, _) => Self::class_object_type("Hash"),
                Type::Proc(_, _) | Type::BoundProc { .. } => Self::class_object_type("Proc"),
                Type::Object => Self::class_object_type("Object"),
                Type::Named(class, _) if name_matches(class, "Array") => {
                    Self::class_object_type("Array")
                }
                Type::Named(class, _) if name_matches(class, "Hash") => {
                    Self::class_object_type("Hash")
                }
                Type::Named(class, _) => Self::class_object_type(class),
                Type::Intersection(_)
                | Type::Union(_)
                | Type::TypeVar(_)
                | Type::AttachedClass
                | Type::AttachedClassOf(_) => Type::Any,
            });
        }
        if Self::class_object_instance_type(receiver).is_some() {
            match name {
                "name" => return Some(Type::union([Type::Nil, Type::String])),
                "===" => return Some(Type::bool()),
                "const_source_location" => {
                    return Some(Type::union([
                        Type::Nil,
                        Type::Tuple(vec![Type::String, Type::Integer]),
                    ]));
                }
                _ => {}
            }
        }
        match name {
            "to_yaml" => return Some(Type::String),
            "freeze" | "dup" | "clone" => return Some(receiver.clone()),
            "method" | "public_method" | "singleton_method" => return Some(Type::named("Method")),
            "id" | "object_id" | "hash" => return Some(Type::Integer),
            "respond_to?" | "frozen?" | "nil?" | "is_a?" | "kind_of?" | "instance_of?" | "=="
            | "!=" | "equal?" | "eql?" | "!" => return Some(Type::bool()),
            "to_s" | "inspect" => return Some(Type::String),
            "to_enum" | "enum_for" => return Some(Type::named("Enumerator")),
            "to_a" => return Some(Type::Array(Box::new(Type::Any))),
            _ => {}
        }
        if *receiver == Type::String && matches!(name, "bytes" | "codepoints") {
            return Some(Type::Array(Box::new(Type::Integer)));
        }
        if name == "[]=" {
            if let (Type::Array(element), Some(Type::Array(replacement))) =
                (receiver, argument_types.last())
            {
                let range_index = argument_types.first().is_some_and(|type_| {
                    matches!(type_, Type::Named(name, arguments) if name_matches(name, "Range") && arguments.len() == 2)
                });
                if range_index && self.is_assignable(replacement, element) {
                    return Some(Type::Array(replacement.clone()));
                }
            }
        }
        if name != "literal_value" {
            return None;
        }
        let instance = Self::class_object_instance_type(receiver)?;
        if !Self::named_type_name(&instance)
            .is_some_and(|name| self.nominal_names_match(&name, "NodeHelpers"))
        {
            return None;
        }
        let argument = argument_types.first()?;
        let is_string_node = match argument {
            Type::Intersection(members) => members.iter().any(|member| {
                Self::named_type_name(member)
                    .is_some_and(|name| name_matches(&name, "AST::StringNode"))
            }),
            _ => Self::named_type_name(argument)
                .is_some_and(|name| name_matches(&name, "AST::StringNode")),
        };
        is_string_node.then_some(Type::String)
    }

    pub(super) fn random_formatter_signature(
        &self,
        receiver_type: &Type,
        name: &str,
    ) -> Option<MethodSig> {
        if name != "alphanumeric" {
            return None;
        }
        let typed_receiver = Self::class_object_instance_type(receiver_type)
            .or_else(|| Some(receiver_type.clone()))
            .and_then(|receiver| Self::named_type_name(&receiver));
        if !typed_receiver
            .as_deref()
            .is_some_and(|name| matches!(name, "Random" | "SecureRandom"))
        {
            return None;
        }
        let mut signature =
            MethodSig::new(vec![Type::union([Type::Nil, Type::Integer])], Type::String);
        signature.required_params = 0;
        signature.keywords.insert(
            "chars".to_owned(),
            signature::KeywordParam {
                type_: Type::Array(Box::new(Type::Any)),
                required: false,
            },
        );
        Some(signature)
    }
}
