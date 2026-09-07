use super::{
    name_matches, nominal_name, prism, proc_parts, proc_receiver, trim_ascii_whitespace, Analyzer,
    Environment,
};
use crate::signature::{self, AssertionKind, MethodSig};
use crate::types::Type;
use ruby_prism::Node;
use std::collections::{BTreeMap, BTreeSet};

impl<'src> Analyzer<'src> {
    pub(crate) fn check_assignable<'node>(
        &mut self,
        node: &Node<'node>,
        actual: &Type,
        expected: &Type,
    ) {
        let actual = self.tuple_literal_argument_type(node, actual, expected);
        if !self.is_assignable(&actual, expected) {
            let attached_class_expected = Self::contains_attached_class_type(expected);
            let actual = if attached_class_expected {
                self.literal_type_description(node, &actual)
            } else {
                actual.to_string()
            };
            if attached_class_expected {
                self.error(node, format!("Expected `{expected}` but found `{actual}`"));
            } else {
                self.error(node, format!("Expected `{expected}`, but found `{actual}`"));
            }
        }
    }

    pub(crate) fn literal_type_description(&self, node: &Node<'_>, type_: &Type) -> String {
        if matches!(type_, Type::String) {
            if let Some(string) = node.as_string_node() {
                let value = String::from_utf8_lossy(string.unescaped());
                return format!("String(\"{value}\")");
            }
        }
        if matches!(type_, Type::Integer) {
            if node.as_integer_node().is_some() {
                return format!("Integer({})", prism::text(self.source, node));
            }
        }
        type_.to_string()
    }

    pub(crate) fn resolve_signature_names(
        &self,
        signature: &MethodSig,
        owner: Option<&str>,
    ) -> MethodSig {
        let mut result = signature.clone();
        result.params = signature
            .params
            .iter()
            .map(|type_| {
                self.resolve_type_names_with_locals(type_, owner, &signature.type_parameters)
            })
            .collect();
        result.return_type = self.resolve_type_names_with_locals(
            &signature.return_type,
            owner,
            &signature.type_parameters,
        );
        result.keywords = signature
            .keywords
            .iter()
            .map(|(name, parameter)| {
                (
                    name.clone(),
                    signature::KeywordParam {
                        type_: self.resolve_type_names_with_locals(
                            &parameter.type_,
                            owner,
                            &signature.type_parameters,
                        ),
                        required: parameter.required,
                    },
                )
            })
            .collect();
        result.block = signature.block.as_ref().map(|block| {
            self.resolve_type_names_with_locals(block, owner, &signature.type_parameters)
        });
        result
    }

    pub(crate) fn resolve_type_names(&self, type_: &Type, owner: Option<&str>) -> Type {
        self.resolve_type_names_with_locals(type_, owner, &[])
    }

    pub(crate) fn resolve_type_names_with_locals(
        &self,
        type_: &Type,
        owner: Option<&str>,
        local_type_parameters: &[String],
    ) -> Type {
        match type_ {
            Type::Symbol
                if owner
                    .and_then(|owner| {
                        let resolved = self.resolve_name("Symbol", Some(owner));
                        (resolved != "Symbol" && self.declarations.classes.contains_key(&resolved))
                            .then_some(resolved)
                    })
                    .is_some() =>
            {
                Type::Named(self.resolve_name("Symbol", owner), Vec::new())
            }
            Type::TypeVar(name)
                if !local_type_parameters
                    .iter()
                    .any(|parameter| parameter == name)
                    && owner.is_some_and(|owner| {
                        self.declarations
                            .classes
                            .get(owner)
                            .is_some_and(|info| info.type_members.contains_key(name))
                    }) =>
            {
                Type::TypeVar(format!(
                    "{}::{name}",
                    owner.expect("owner is present for a type member")
                ))
            }
            Type::TypeVar(name)
                if !local_type_parameters
                    .iter()
                    .any(|parameter| parameter == name)
                    && (self.declarations.classes.contains_key(name)
                        || self.declarations.constants.contains_key(name)) =>
            {
                Type::Named(self.resolve_name(name, owner), Vec::new())
            }
            Type::Named(name, arguments) => {
                if arguments.is_empty()
                    && owner.is_some_and(|owner| {
                        self.declarations
                            .classes
                            .get(owner)
                            .is_some_and(|info| info.type_members.contains_key(name))
                    })
                {
                    return Type::TypeVar(format!(
                        "{}::{name}",
                        owner.expect("owner is present for a type member")
                    ));
                }
                if arguments.is_empty() {
                    if let Some((alias_name, alias_type)) = self.find_type_alias(name, owner) {
                        if alias_type != *type_ {
                            let alias_owner = alias_name.rsplit_once("::").map(|(scope, _)| scope);
                            return self.resolve_type_names_with_locals(
                                &alias_type,
                                alias_owner.or(owner),
                                local_type_parameters,
                            );
                        }
                    }
                }
                let resolved = if name == "instance" && arguments.is_empty() {
                    name.clone()
                } else {
                    self.resolve_name(name, owner)
                };
                let arguments = if arguments.is_empty()
                    && (name_matches(&resolved, "Class") || name_matches(&resolved, "Module"))
                {
                    vec![Type::Anything]
                } else {
                    arguments
                        .iter()
                        .map(|argument| {
                            self.resolve_type_names_with_locals(
                                argument,
                                owner,
                                local_type_parameters,
                            )
                        })
                        .collect()
                };
                Type::Named(resolved, arguments)
            }
            Type::Array(element) => Type::Array(Box::new(self.resolve_type_names_with_locals(
                element,
                owner,
                local_type_parameters,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(self.resolve_type_names_with_locals(key, owner, local_type_parameters)),
                Box::new(self.resolve_type_names_with_locals(value, owner, local_type_parameters)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        self.resolve_type_names_with_locals(element, owner, local_type_parameters)
                    })
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| {
                        self.resolve_type_names_with_locals(parameter, owner, local_type_parameters)
                    })
                    .collect(),
                Box::new(self.resolve_type_names_with_locals(result, owner, local_type_parameters)),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(self.resolve_type_names_with_locals(
                    receiver,
                    owner,
                    local_type_parameters,
                )),
                parameters: parameters
                    .iter()
                    .map(|parameter| {
                        self.resolve_type_names_with_locals(parameter, owner, local_type_parameters)
                    })
                    .collect(),
                result: Box::new(self.resolve_type_names_with_locals(
                    result,
                    owner,
                    local_type_parameters,
                )),
            },
            Type::Union(members) => Type::union(members.iter().map(|member| {
                self.resolve_type_names_with_locals(member, owner, local_type_parameters)
            })),
            Type::Intersection(members) => Type::intersection(members.iter().map(|member| {
                self.resolve_type_names_with_locals(member, owner, local_type_parameters)
            })),
            other => other.clone(),
        }
    }

    pub(crate) fn find_type_alias(
        &self,
        name: &str,
        owner: Option<&str>,
    ) -> Option<(String, Type)> {
        let name = name.trim_start_matches("::");
        let matches = |candidate: &str| candidate == name;
        if let Some((key, type_)) = self
            .declarations
            .type_aliases
            .iter()
            .find(|(key, _)| matches(key))
        {
            return Some((key.clone(), type_.clone()));
        }

        let mut scope = owner;
        while let Some(current) = scope {
            let candidate = format!("{current}::{name}");
            if let Some((key, type_)) = self
                .declarations
                .type_aliases
                .iter()
                .find(|(key, _)| key.as_str() == candidate)
            {
                return Some((key.clone(), type_.clone()));
            }
            scope = current.rsplit_once("::").map(|(parent, _)| parent);
        }

        let qualified_suffix = format!("::{name}");
        let mut qualified = self
            .declarations
            .type_aliases
            .iter()
            .filter(|(key, _)| key.ends_with(&qualified_suffix));
        if let Some((key, type_)) = qualified.next() {
            if qualified.next().is_none() {
                return Some((key.clone(), type_.clone()));
            }
        }

        let name_tail = name.rsplit_once("::").map_or(name, |(_, tail)| tail);
        let mut candidates = self.declarations.type_aliases.iter().filter(|(key, _)| {
            let candidate_tail = key.rsplit_once("::").map_or(key.as_str(), |(_, tail)| tail);
            // RBS comments currently retain aliases without their lexical
            // owner. Preserve the compatibility fallback for an exactly
            // matching tail, but respect Ruby/RBS case sensitivity: `status`
            // must not capture `Process::Status`.
            candidate_tail == name_tail
        });
        let (key, type_) = candidates.next()?;
        if candidates.next().is_some() {
            None
        } else {
            Some((key.clone(), type_.clone()))
        }
    }

    pub(crate) fn resolve_name(&self, name: &str, owner: Option<&str>) -> String {
        let absolute = name.starts_with("::");
        let name = name.trim_start_matches("::");
        if absolute {
            return name.to_owned();
        }
        let mut scope = owner;
        while let Some(current) = scope {
            let candidate = format!("{current}::{name}");
            if self.declarations.classes.contains_key(&candidate)
                || self.declarations.constants.contains_key(&candidate)
            {
                return candidate;
            }
            scope = current.rsplit_once("::").map(|(parent, _)| parent);
        }
        if self.declarations.classes.contains_key(name)
            || self.declarations.constants.contains_key(name)
        {
            return name.to_owned();
        }
        name.to_owned()
    }

    pub(crate) fn add_name_suffixes(index: &mut BTreeMap<String, Vec<String>>, name: &str) {
        let mut start = 0;
        loop {
            index
                .entry(name[start..].to_owned())
                .or_default()
                .push(name.to_owned());
            let Some(separator) = name[start..].find("::") else {
                break;
            };
            start += separator + 2;
        }
    }

    pub(crate) fn rebuild_nominal_name_indexes(&mut self) {
        self.declarations.class_name_set.clear();
        self.declarations.constant_name_set.clear();
        self.declarations.class_name_suffixes.clear();
        self.declarations.constant_name_suffixes.clear();
        let class_names = self
            .declarations
            .classes
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for name in class_names {
            self.declarations.class_name_set.insert(name.clone());
            Self::add_name_suffixes(&mut self.declarations.class_name_suffixes, &name);
        }
        let constant_names = self
            .declarations
            .constants
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for name in constant_names {
            self.declarations.constant_name_set.insert(name.clone());
            Self::add_name_suffixes(&mut self.declarations.constant_name_suffixes, &name);
        }
    }

    pub(crate) fn resolve_global_name(&self, name: &str) -> String {
        if self.declarations.class_name_set.contains(name)
            || self.declarations.constant_name_set.contains(name)
        {
            return name.to_owned();
        }
        if let Some(resolved) = self.global_name_cache.borrow().get(name) {
            return resolved.clone();
        }
        let resolved = if let Some(matches) = self.declarations.class_name_suffixes.get(name) {
            if matches.len() == 1 {
                matches[0].clone()
            } else {
                name.to_owned()
            }
        } else {
            name.to_owned()
        };
        self.global_name_cache
            .borrow_mut()
            .insert(name.to_owned(), resolved.clone());
        resolved
    }

    pub(crate) fn each_nominal_name_candidate<F>(&self, name: &str, mut visit: F) -> bool
    where
        F: FnMut(&str) -> bool,
    {
        if self.declarations.class_name_set.contains(name)
            || self.declarations.constant_name_set.contains(name)
        {
            return visit(name);
        }

        let mut found = false;
        if let Some(candidates) = self.declarations.class_name_suffixes.get(name) {
            found = true;
            for candidate in candidates {
                if visit(candidate) {
                    return true;
                }
            }
        }
        if let Some(candidates) = self.declarations.constant_name_suffixes.get(name) {
            found = true;
            for candidate in candidates {
                if visit(candidate) {
                    return true;
                }
            }
        }
        if !found {
            visit(name)
        } else {
            false
        }
    }

    pub(crate) fn nominal_names_match(&self, actual: &str, expected: &str) -> bool {
        if nominal_name(actual) == nominal_name(expected) {
            return true;
        }
        if self.each_nominal_name_candidate(actual, |actual| {
            self.each_nominal_name_candidate(expected, |expected| {
                nominal_name(actual) == nominal_name(expected)
            })
        }) {
            return true;
        }
        let actual = self.resolve_global_name(actual);
        let expected = self.resolve_global_name(expected);
        actual == expected
            || (self.declarations.class_name_set.contains(&actual)
                && Self::qualified_name_ends_with(&expected, &actual))
            || (self.declarations.class_name_set.contains(&expected)
                && Self::qualified_name_ends_with(&actual, &expected))
    }

    pub(crate) fn qualified_name_ends_with(name: &str, suffix: &str) -> bool {
        name.len() >= suffix.len() + 2
            && name.ends_with(suffix)
            && name.as_bytes()[name.len() - suffix.len() - 2..].starts_with(b"::")
    }

    pub(crate) fn normalize_class_graph(&mut self) {
        let owners = self
            .declarations
            .classes
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for owner in owners {
            let Some(info) = self.declarations.classes.get(&owner).cloned() else {
                continue;
            };
            let superclass = info
                .superclass
                .as_deref()
                .map(|name| {
                    let name = name.trim_start_matches("::");
                    if name.contains("::")
                        && (self.declarations.classes.contains_key(name)
                            || self.declarations.constants.contains_key(name))
                    {
                        name.to_owned()
                    } else {
                        self.resolve_name(name, Some(&owner))
                    }
                })
                .or_else(|| {
                    // Ruby classes without an explicit superclass inherit
                    // from Object.  Keeping that implicit edge matters for
                    // ordinary Kernel/Object APIs such as `block_given?`,
                    // `send`, and `singleton_class`.
                    (!info.is_module && !matches!(owner.as_str(), "Object" | "BasicObject"))
                        .then(|| "Object".to_owned())
                });
            let includes = info
                .includes
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            let prepends = info
                .prepends
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            let extends = info
                .extends
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            let class_methods = info
                .class_methods
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            let requires_ancestors = info
                .requires_ancestors
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            if let Some(info) = self.declarations.classes.get_mut(&owner) {
                info.superclass = superclass;
                info.includes = includes;
                info.prepends = prepends;
                info.extends = extends;
                info.class_methods = class_methods;
                info.requires_ancestors = requires_ancestors;
            }
        }

        let concern_class_methods = self
            .declarations
            .classes
            .iter()
            .filter_map(|(owner, info)| {
                let is_concern = info
                    .extends
                    .iter()
                    .any(|extension| extension == "ActiveSupport::Concern");
                let class_methods = format!("{owner}::ClassMethods");
                (is_concern && self.declarations.classes.contains_key(&class_methods))
                    .then_some((owner.clone(), class_methods))
            })
            .collect::<BTreeMap<_, _>>();
        let mixins = self
            .declarations
            .classes
            .iter()
            .map(|(owner, info)| {
                let mut includes = info.includes.clone();
                includes.extend(info.prepends.clone());
                (owner.clone(), includes)
            })
            .collect::<Vec<_>>();
        for (owner, includes) in mixins {
            let explicit_class_methods = includes
                .iter()
                .flat_map(|included| {
                    self.declarations
                        .classes
                        .get(included)
                        .into_iter()
                        .flat_map(|info| info.class_methods.iter().cloned())
                })
                .collect::<Vec<_>>();
            let concern_mixin_methods = includes
                .iter()
                .filter_map(|included| concern_class_methods.get(included).cloned())
                .collect::<Vec<_>>();
            if let Some(info) = self.declarations.classes.get_mut(&owner) {
                for class_method in explicit_class_methods
                    .into_iter()
                    .chain(concern_mixin_methods)
                {
                    if !info.extends.contains(&class_method) {
                        info.extends.push(class_method);
                    }
                }
            }
        }
    }

    pub(crate) fn is_assignable(&self, actual: &Type, expected: &Type) -> bool {
        let resolved_actual = self.resolve_type_names(actual, None);
        let resolved_expected = self.resolve_type_names(expected, None);
        if resolved_actual != *actual || resolved_expected != *expected {
            return self.is_assignable(&resolved_actual, &resolved_expected);
        }
        if actual.is_any() || expected.is_any() || actual.is_never() {
            return true;
        }
        if actual == expected || actual.is_subtype_of(expected) {
            return true;
        }
        match (actual, expected) {
            (Type::Union(actual_members), Type::Union(expected_members)) => {
                return actual_members.iter().all(|actual| {
                    expected_members
                        .iter()
                        .any(|expected| self.is_assignable(actual, expected))
                });
            }
            (Type::Union(actual_members), _) => {
                return actual_members
                    .iter()
                    .all(|member| self.is_assignable(member, expected));
            }
            (_, Type::Union(expected_members)) => {
                return expected_members
                    .iter()
                    .any(|member| self.is_assignable(actual, member));
            }
            _ => {}
        }
        if let Type::Intersection(expected_members) = expected {
            return expected_members
                .iter()
                .all(|member| self.is_assignable(actual, member));
        }
        if let Type::Intersection(actual_members) = actual {
            return actual_members
                .iter()
                .any(|member| self.is_assignable(member, expected));
        }
        match (actual, expected) {
            (Type::AttachedClassOf(actual), Type::Named(expected, _)) => {
                self.nominal_subtype(actual, expected)
            }
            (Type::AttachedClassOf(actual), Type::AttachedClassOf(expected)) => {
                self.nominal_subtype(actual, expected)
            }
            (Type::Array(actual), Type::Array(expected)) => self.is_assignable(actual, expected),
            (Type::Hash(actual_key, actual_value), Type::Hash(expected_key, expected_value)) => {
                self.is_assignable(actual_key, expected_key)
                    && self.is_assignable(actual_value, expected_value)
            }
            (Type::Tuple(actual), Type::Tuple(expected)) => {
                actual.len() == expected.len()
                    && actual
                        .iter()
                        .zip(expected)
                        .all(|(actual, expected)| self.is_assignable(actual, expected))
            }
            (Type::Array(actual), Type::Tuple(expected)) => expected
                .iter()
                .all(|expected| self.is_assignable(actual, expected)),
            (Type::Tuple(actual), Type::Array(expected)) => actual
                .iter()
                .all(|actual| self.is_assignable(actual, expected)),
            (_, Type::Named(name, arguments))
                if arguments.is_empty() && name_matches(name, "BasicObject") =>
            {
                true
            }
            (Type::Array(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Enumerable") =>
            {
                self.is_assignable(actual, &arguments[0])
            }
            (Type::Tuple(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Enumerable") =>
            {
                actual
                    .iter()
                    .all(|actual| self.is_assignable(actual, &arguments[0]))
            }
            (Type::Array(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Array") =>
            {
                self.is_assignable(actual, &arguments[0])
            }
            (Type::Array(_) | Type::Tuple(_), Type::Named(name, arguments))
                if arguments.is_empty() && name_matches(name, "Array") =>
            {
                true
            }
            (Type::Tuple(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Array") =>
            {
                actual
                    .iter()
                    .all(|actual| self.is_assignable(actual, &arguments[0]))
            }
            (Type::Named(actual, _), Type::Array(_)) if self.nominal_subtype(actual, "Array") => {
                true
            }
            (Type::Hash(actual_key, actual_value), Type::Named(name, arguments))
                if arguments.len() == 2 && name_matches(name, "Hash") =>
            {
                self.is_assignable(actual_key, &arguments[0])
                    && self.is_assignable(actual_value, &arguments[1])
            }
            (Type::Named(actual, _), Type::Hash(_, _)) if self.nominal_subtype(actual, "Hash") => {
                true
            }
            (
                Type::Proc(actual_params, actual_return),
                Type::Proc(expected_params, expected_return),
            ) => {
                actual_params.len() == expected_params.len()
                    && actual_params
                        .iter()
                        .zip(expected_params)
                        .all(|(actual, expected)| self.is_assignable(expected, actual))
                    && self.is_assignable(actual_return, expected_return)
            }
            (
                actual @ (Type::Proc(_, _) | Type::BoundProc { .. }),
                expected @ (Type::Proc(_, _) | Type::BoundProc { .. }),
            ) => {
                let Some((actual_params, actual_return)) = proc_parts(actual) else {
                    return false;
                };
                let Some((expected_params, expected_return)) = proc_parts(expected) else {
                    return false;
                };
                let receiver_compatible = match (proc_receiver(actual), proc_receiver(expected)) {
                    (Some(actual), Some(expected)) => self.is_assignable(actual, expected),
                    (Some(_), None) => true,
                    (None, Some(_)) => false,
                    (None, None) => true,
                };
                receiver_compatible
                    && actual_params.len() == expected_params.len()
                    && actual_params
                        .iter()
                        .zip(expected_params)
                        .all(|(actual, expected)| self.is_assignable(expected, actual))
                    && self.is_assignable(actual_return, expected_return)
            }
            (Type::Named(actual_name, actual_args), Type::Named(expected_name, expected_args))
                if actual_args.len() == 1
                    && expected_args.is_empty()
                    && name_matches(actual_name, "Class")
                    && name_matches(expected_name, "Module") =>
            {
                true
            }
            (Type::Named(actual_name, actual_args), Type::Named(expected_name, expected_args)) => {
                if actual_args.len() == 2
                    && expected_args.len() == 1
                    && name_matches(actual_name, "Range")
                    && name_matches(expected_name, "Range")
                {
                    // Range literals retain the types of their begin and end
                    // expressions as two internal arguments. Sorbet's
                    // `T::Range[Element]` describes the same value by the
                    // common element type. A beginless or endless range has
                    // NilClass for its missing endpoint, which is still a
                    // valid range of the other endpoint's element type.
                    return actual_args.iter().all(|actual| {
                        actual.is_nil() || self.is_assignable(actual, &expected_args[0])
                    });
                }
                if self.nominal_names_match(actual_name, expected_name) {
                    expected_args.is_empty()
                        || actual_args.is_empty()
                        || (actual_args.len() == expected_args.len()
                            && actual_args
                                .iter()
                                .zip(expected_args)
                                .all(|(actual, expected)| self.is_assignable(actual, expected)))
                } else {
                    self.nominal_subtype(actual_name, expected_name)
                        && (expected_args.is_empty()
                            || actual_args.is_empty()
                            || (actual_args.len() == expected_args.len()
                                && actual_args.iter().zip(expected_args).all(
                                    |(actual, expected)| self.is_assignable(actual, expected),
                                )))
                }
            }
            (Type::Named(actual, _), Type::Integer) if self.nominal_subtype(actual, "Integer") => {
                true
            }
            (Type::Named(actual, _), Type::Float) if self.nominal_subtype(actual, "Float") => true,
            (Type::Named(actual, _), Type::String) if self.nominal_subtype(actual, "String") => {
                true
            }
            (Type::Named(actual, _), Type::Symbol) if self.nominal_subtype(actual, "Symbol") => {
                true
            }
            (actual, Type::Named(expected, arguments))
                if arguments.is_empty()
                    && Self::primitive_nominal_name(actual)
                        .is_some_and(|actual| self.nominal_subtype(actual, expected)) =>
            {
                true
            }
            _ => false,
        }
    }

    pub(crate) fn primitive_nominal_name(type_: &Type) -> Option<&'static str> {
        match type_ {
            Type::Nil => Some("NilClass"),
            Type::True => Some("TrueClass"),
            Type::False => Some("FalseClass"),
            Type::Integer => Some("Integer"),
            Type::Float => Some("Float"),
            Type::String => Some("String"),
            Type::Symbol => Some("Symbol"),
            Type::Object => Some("Object"),
            _ => None,
        }
    }

    pub(crate) fn nominal_subtype(&self, actual: &str, expected: &str) -> bool {
        if self.each_nominal_name_candidate(expected, |expected| {
            nominal_name(expected) == "BasicObject"
        }) {
            return true;
        }
        self.each_nominal_name_candidate(actual, |actual| {
            self.each_nominal_name_candidate(expected, |expected| {
                self.nominal_subtype_names(nominal_name(actual), nominal_name(expected))
            })
        })
    }

    pub(crate) fn nominal_subtype_names(&self, actual: &str, expected: &str) -> bool {
        if actual == expected {
            return true;
        }
        let mut pending = vec![actual.to_owned()];
        let mut visited = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if name == expected {
                return true;
            }
            if let Some(superclass) = Self::builtin_superclass(&name) {
                pending.push(superclass.to_owned());
            }
            let Some(info) = self.declarations.classes.get(&name) else {
                continue;
            };
            if let Some(superclass) = &info.superclass {
                pending.push(nominal_name(superclass).to_owned());
            }
            pending.extend(
                info.includes
                    .iter()
                    .map(|include| nominal_name(include).to_owned()),
            );
            pending.extend(
                info.prepends
                    .iter()
                    .map(|prepend| nominal_name(prepend).to_owned()),
            );
        }
        false
    }

    pub(crate) fn builtin_superclass(name: &str) -> Option<&'static str> {
        match name.rsplit_once("::").map_or(name, |(_, tail)| tail) {
            "StandardError" => Some("Exception"),
            "ArgumentError" | "EncodingError" | "FiberError" | "IOError" | "IndexError"
            | "KeyError" | "LocalJumpError" | "NameError" | "NoMethodError" | "RangeError"
            | "RegexpError" | "RuntimeError" | "StopIteration" | "SystemCallError"
            | "TypeError" | "ZeroDivisionError" => Some("StandardError"),
            "EOFError" => Some("IOError"),
            "FloatDomainError" => Some("RangeError"),
            _ => None,
        }
    }

    pub(crate) fn apply_inline_assertion<'node>(
        &mut self,
        node: &Node<'node>,
        actual: Type,
    ) -> Type {
        if self.defer_inline_assertions {
            return actual;
        }
        let assertion = self.inline_assertion_for_node(node);
        let Some(assertion) = assertion else {
            return actual;
        };
        let expected = self.resolve_type_names(&assertion.type_, None);
        match assertion.kind {
            AssertionKind::Let => {
                self.check_assignable(node, &actual, &expected);
                expected
            }
            AssertionKind::Cast => expected,
            AssertionKind::SelfAs => actual,
            AssertionKind::Must => {
                if actual.is_nil() {
                    self.error(node, "Expected a non-nil value");
                }
                actual.without(&Type::Nil)
            }
            AssertionKind::Unsafe => Type::Any,
            AssertionKind::Absurd => {
                if !actual.is_never() {
                    self.error(node, format!("Expected `T.noreturn`, but found `{actual}`"));
                }
                Type::Never
            }
        }
    }

    pub(crate) fn apply_inline_assertion_in_environment<'node>(
        &mut self,
        node: &Node<'node>,
        actual: Type,
        environment: &Environment,
    ) -> Type {
        if self.defer_inline_assertions {
            return actual;
        }
        let assertion = self.inline_assertion_for_node(node);
        let Some(assertion) = assertion else {
            return actual;
        };
        let owner = self.lexical_owner(environment);
        let expected = self.resolve_shadowed_builtin_types(&assertion.type_, owner.as_deref());
        match assertion.kind {
            AssertionKind::Let => {
                self.check_assignable(node, &actual, &expected);
                expected
            }
            AssertionKind::Cast => expected,
            AssertionKind::SelfAs => actual,
            AssertionKind::Must => {
                if actual.is_nil() {
                    self.error(node, "Expected a non-nil value");
                }
                actual.without(&Type::Nil)
            }
            AssertionKind::Unsafe => Type::Any,
            AssertionKind::Absurd => {
                if !actual.is_never() {
                    self.error(node, format!("Expected `T.noreturn`, but found `{actual}`"));
                }
                Type::Never
            }
        }
    }

    pub(crate) fn inline_assertion_for_node<'node>(
        &self,
        node: &Node<'node>,
    ) -> Option<crate::signature::InlineAssertion> {
        if !self.has_inline_assertions {
            return None;
        }
        let (start, end) = prism::span(node);
        let start_line = self.line_map.line_number(start);
        let end_line = self.line_map.line_number(end.saturating_sub(1));
        if let Some(assertion) = [start_line, end_line]
            .into_iter()
            .filter_map(|line| self.annotations.assertions.get(&line))
            .find(|assertion| {
                assertion.offset >= end
                    && self.source[end..assertion.offset]
                        .iter()
                        .all(|byte| byte.is_ascii_whitespace() || *byte == b',')
            })
            .cloned()
        {
            return Some(assertion);
        }

        // Spoom emits `#: self as Type` on the line before the expression it
        // narrows. Permit blank lines between that comment and the expression
        // while keeping ordinary comments from reaching arbitrarily far.
        for line in (0..start_line).rev() {
            let Some(line_start) = self.line_map.line_start(line) else {
                break;
            };
            let line_end = self
                .line_map
                .line_start(line + 1)
                .map_or(self.source.len(), |next| next.saturating_sub(1));
            let trimmed = trim_ascii_whitespace(
                self.source
                    .get(line_start..line_end.min(self.source.len()))
                    .unwrap_or_default(),
            );
            if trimmed.is_empty() {
                continue;
            }
            let Some(assertion) = self.annotations.assertions.get(&line) else {
                break;
            };
            if assertion.kind == AssertionKind::SelfAs && trimmed.starts_with(b"#") {
                return Some(assertion.clone());
            }
            break;
        }
        None
    }

    pub(crate) fn resolve_shadowed_builtin_types(&self, type_: &Type, owner: Option<&str>) -> Type {
        match type_ {
            Type::Symbol => owner
                .and_then(|owner| {
                    let resolved = self.resolve_name("Symbol", Some(owner));
                    (resolved != "Symbol" && self.declarations.classes.contains_key(&resolved))
                        .then_some(Type::named(resolved))
                })
                .unwrap_or(Type::Symbol),
            Type::Array(element) => Type::Array(Box::new(
                self.resolve_shadowed_builtin_types(element, owner),
            )),
            Type::Hash(key, value) => Type::Hash(
                Box::new(self.resolve_shadowed_builtin_types(key, owner)),
                Box::new(self.resolve_shadowed_builtin_types(value, owner)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| self.resolve_shadowed_builtin_types(element, owner))
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| self.resolve_shadowed_builtin_types(parameter, owner))
                    .collect(),
                Box::new(self.resolve_shadowed_builtin_types(result, owner)),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(self.resolve_shadowed_builtin_types(receiver, owner)),
                parameters: parameters
                    .iter()
                    .map(|parameter| self.resolve_shadowed_builtin_types(parameter, owner))
                    .collect(),
                result: Box::new(self.resolve_shadowed_builtin_types(result, owner)),
            },
            Type::Named(name, arguments) => self.resolve_type_names(
                &Type::Named(
                    name.clone(),
                    arguments
                        .iter()
                        .map(|argument| self.resolve_shadowed_builtin_types(argument, owner))
                        .collect(),
                ),
                owner,
            ),
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.resolve_shadowed_builtin_types(member, owner)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| self.resolve_shadowed_builtin_types(member, owner)),
            ),
            other => other.clone(),
        }
    }

    pub(crate) fn type_from_node<'node>(&self, node: &Node<'node>) -> Type {
        signature::parse_type(&prism::text(self.source, node))
    }

    pub(crate) fn runtime_type_object_type<'node>(&self, node: &Node<'node>) -> Type {
        let source = prism::text(self.source, node);
        let expression = source.trim().trim_start_matches("::");
        let class = if expression.starts_with("T.proc") {
            "T::Types::Proc"
        } else if expression.starts_with("T.nilable(") || expression.starts_with("T.any(") {
            "T::Types::Union"
        } else if expression.starts_with("T.all(") {
            "T::Types::Intersection"
        } else if expression.starts_with("T.class_of(") {
            "T::Types::ClassOf"
        } else if expression.starts_with("T.noreturn") {
            "T::Types::NoReturn"
        } else if expression.starts_with("T.untyped") {
            "T::Types::Untyped"
        } else if expression.starts_with("T.anything") {
            "T::Types::Anything"
        } else {
            "T::Types::Base"
        };
        Type::named(class)
    }

    pub(crate) fn constant_reference_name<'node>(&self, node: &Node<'node>) -> Option<String> {
        if let Some(constant) = node.as_constant_read_node() {
            return Some(prism::constant_name(constant.name()));
        }
        if let Some(path) = node.as_constant_path_node() {
            return Some(self.constant_path_name(&path));
        }
        None
    }

    pub(crate) fn constant_path_name<'node>(
        &self,
        path: &ruby_prism::ConstantPathNode<'node>,
    ) -> String {
        let absolute = prism::text(self.source, &path.as_node())
            .trim_start()
            .starts_with("::");
        let name = path.name().map_or_else(String::new, prism::constant_name);
        let name = match path.parent() {
            Some(parent) => {
                let parent = self
                    .constant_reference_name(&parent)
                    .unwrap_or_else(|| prism::text(self.source, &parent));
                if parent.is_empty() {
                    name
                } else {
                    format!("{parent}::{name}")
                }
            }
            None => name,
        };
        if absolute {
            format!("::{name}")
        } else {
            name
        }
    }

    pub(crate) fn numeric_sum_type(element: &Type, initial: Option<&Type>) -> Type {
        let mut saw_float = false;
        for type_ in [Some(element), initial].into_iter().flatten() {
            let mut pending = vec![type_];
            while let Some(type_) = pending.pop() {
                match type_ {
                    Type::Integer => {}
                    Type::Float => saw_float = true,
                    Type::Union(members) => pending.extend(members),
                    Type::Never => {}
                    _ => return Type::Any,
                }
            }
        }
        if saw_float {
            Type::Float
        } else {
            Type::Integer
        }
    }

    pub(crate) fn array_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => element.as_ref().clone(),
            Type::Tuple(elements) => {
                let element = elements
                    .iter()
                    .fold(Type::Never, |current, element| current.join(element));
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            Type::Union(members) => {
                let mut element = Type::Never;
                for member in members {
                    element = element.join(&self.array_element_type(member));
                }
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            _ => Type::Any,
        }
    }

    pub(crate) fn pair_types(type_: &Type) -> Option<(Type, Type)> {
        match type_ {
            Type::Tuple(elements) if elements.len() == 2 => {
                Some((elements[0].clone(), elements[1].clone()))
            }
            Type::Array(element) => Self::pair_types(element),
            Type::Union(members) => {
                let mut pairs = members.iter().map(Self::pair_types);
                let (mut key, mut value) = pairs.next()??;
                for pair in pairs {
                    let (next_key, next_value) = pair?;
                    key = key.join(&next_key);
                    value = value.join(&next_value);
                }
                Some((key, value))
            }
            _ => None,
        }
    }

    pub(crate) fn flat_map_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => element.as_ref().clone(),
            Type::Tuple(elements) => {
                let element = elements
                    .iter()
                    .fold(Type::Never, |current, element| current.join(element));
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            Type::Union(members) => {
                let element = members.iter().fold(Type::Never, |current, member| {
                    current.join(&self.flat_map_element_type(member))
                });
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            other => other.clone(),
        }
    }

    pub(crate) fn flattened_array_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => self.flattened_array_element_type(element),
            Type::Tuple(elements) => {
                let element = elements.iter().fold(Type::Never, |current, element| {
                    current.join(&self.flattened_array_element_type(element))
                });
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            Type::Union(members) => {
                let element = members.iter().fold(Type::Never, |current, member| {
                    current.join(&self.flattened_array_element_type(member))
                });
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            other => other.clone(),
        }
    }
}
