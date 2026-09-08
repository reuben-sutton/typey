use super::{name_matches, optional_proc_type, proc_parts, Analyzer, CallArguments, MethodKey};
use crate::signature::{self, MethodSig};
use crate::types::Type;
use std::collections::{BTreeMap, BTreeSet};

impl<'src> Analyzer<'src> {
    pub(super) fn class_object_type(name: &str) -> Type {
        Type::Named("Class".to_owned(), vec![Type::named(name)])
    }

    pub(super) fn class_object_instance_type(type_: &Type) -> Option<Type> {
        match type_ {
            Type::Named(name, arguments)
                if name_matches(name, "Class") || name_matches(name, "Module") =>
            {
                arguments.first().cloned()
            }
            _ => None,
        }
    }

    /// Return the instance types represented by a class-object union. A
    /// callback such as `included(base)` can observe several different class
    /// objects across a workspace, so its inferred parameter is commonly
    /// `Class[A] | Class[B]`. Mixin operations still apply independently to
    /// every member of that union.
    pub(super) fn class_object_instance_types(type_: &Type) -> Option<Vec<Type>> {
        if let Some(instance) = Self::class_object_instance_type(type_) {
            return match instance {
                // Type joining represents `Class[A] | Class[B]` as
                // `Class[A | B]`. Preserve the individual possible classes
                // so a forwarded `base.extend(...)` can update both.
                Type::Union(members) => (!members.is_empty()).then_some(members),
                instance => Some(vec![instance]),
            };
        }
        let Type::Union(members) = type_ else {
            return None;
        };
        let mut instances = Vec::with_capacity(members.len());
        for member in members {
            instances.push(Self::class_object_instance_type(member)?);
        }
        (!instances.is_empty()).then_some(instances)
    }

    pub(super) fn named_type_name(type_: &Type) -> Option<String> {
        match type_ {
            Type::Named(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    pub(super) fn class_object_owner(type_: &Type) -> Option<String> {
        Self::class_object_instance_type(type_)
            .and_then(|instance| Self::named_type_name(&instance))
    }

    pub(super) fn class_object_value_type(type_: &Type) -> Option<Type> {
        let instance = Self::class_object_instance_type(type_)?;
        let builtin = match &instance {
            Type::Named(name, arguments) if arguments.is_empty() => {
                // A project namespace may define a class whose short name
                // matches a Ruby primitive (for example
                // `Spoom::Model::Symbol`).  Only the actual top-level
                // builtins have structural primitive semantics; otherwise
                // `Some(Symbol.new)` would incorrectly become the language's
                // built-in `Symbol` type.
                match name.as_str() {
                    "Integer" => Some(Type::Integer),
                    "Float" => Some(Type::Float),
                    "String" => Some(Type::String),
                    "Symbol" => Some(Type::Symbol),
                    "NilClass" => Some(Type::Nil),
                    "TrueClass" => Some(Type::True),
                    "FalseClass" => Some(Type::False),
                    "Object" | "BasicObject" => Some(Type::Object),
                    _ => None,
                }
            }
            _ => None,
        };
        Some(builtin.unwrap_or(instance))
    }

    pub(super) fn instantiate_generic_class(&self, type_: Type) -> Type {
        let Type::Named(name, arguments) = &type_ else {
            return type_;
        };
        if !arguments.is_empty() {
            return type_;
        }
        let Some(info) = self.declarations.classes.get(name) else {
            return type_;
        };
        if info.type_members.is_empty() {
            return type_;
        }
        if let Some(Type::Named(expected_name, expected_arguments)) =
            self.expected_return_type.as_ref()
        {
            if name_matches(name, expected_name)
                && expected_arguments.len() == info.type_members.len()
            {
                return Type::Named(expected_name.clone(), expected_arguments.clone());
            }
        }
        let mut arguments = vec![Type::Any; info.type_members.len()];
        for member in info.type_members.values() {
            arguments[member.index] = member.fixed.as_ref().map_or(Type::Any, |fixed| {
                self.resolve_type_names(fixed, Some(name))
            });
        }
        match name.as_str() {
            "Array" if arguments.len() == 1 => Type::Array(Box::new(arguments[0].clone())),
            "Hash" if arguments.len() == 2 => Type::Hash(
                Box::new(arguments[0].clone()),
                Box::new(arguments[1].clone()),
            ),
            _ => Type::Named(name.clone(), arguments),
        }
    }

    /// `Class#new` is generic in the core RBI, but an ordinary class object
    /// constructs an instance of the class it represents unless that class
    /// declares its own singleton `new`. Keep that nominal identity in the
    /// owned CFG call path just as the recursive evaluator does.
    pub(super) fn default_class_constructor_type(&self, receiver: &Type, fallback: Type) -> Type {
        let instance = if let Some(instance) = Self::class_object_instance_type(receiver) {
            instance
        } else if let Type::Named(owner, arguments) = receiver {
            Type::Named(owner.clone(), arguments.clone())
        } else {
            return fallback;
        };
        let Some(owner) = Self::named_type_name(&instance) else {
            return fallback;
        };
        let has_explicit_new = Self::class_object_instance_type(receiver).is_some_and(|_| {
            let key = MethodKey {
                owner: Some(owner.clone()),
                name: "new".to_owned(),
                singleton: true,
            };
            self.resolve_method_key(&key)
                .is_some_and(|resolved| resolved.owner.as_deref() == Some(owner.as_str()))
        });
        if has_explicit_new {
            fallback
        } else {
            instance
        }
    }

    pub(super) fn receiver_instance_type(type_: &Type) -> Type {
        if let Some(instance) = Self::class_object_instance_type(type_) {
            return instance;
        }
        if let Type::AttachedClassOf(owner) = type_ {
            return Type::named(owner.clone());
        }
        if let Type::Union(members) = type_ {
            return Type::union(members.iter().map(Self::receiver_instance_type));
        }
        if let Type::Intersection(members) = type_ {
            return Type::intersection(members.iter().map(Self::receiver_instance_type));
        }
        type_.clone()
    }

    pub(super) fn instance_self_type(&self, owner: &str) -> Type {
        if let Some(type_) = self.instance_self_type_cache.borrow().get(owner) {
            return type_.clone();
        }
        let type_ = if self
            .declarations
            .classes
            .get(owner)
            .is_some_and(|info| info.is_module)
        {
            let hosts = self
                .declarations
                .classes
                .iter()
                .filter_map(|(candidate, info)| {
                    info.includes
                        .iter()
                        .any(|included| {
                            included == owner || self.nominal_names_match(included, owner)
                        })
                        .then(|| Type::named(candidate.clone()))
                })
                .collect::<Vec<_>>();
            if hosts.is_empty() {
                Type::named(owner)
            } else {
                Type::union(hosts)
            }
        } else {
            let mut descendants = Vec::new();
            for (candidate, info) in &self.declarations.classes {
                let mut superclass = info.superclass.clone();
                let mut visited = BTreeSet::new();
                while let Some(current) = superclass {
                    if !visited.insert(current.clone()) {
                        break;
                    }
                    if current == owner || self.nominal_names_match(&current, owner) {
                        descendants.push(Type::named(candidate.clone()));
                        break;
                    }
                    superclass = self
                        .declarations
                        .classes
                        .get(&current)
                        .and_then(|info| info.superclass.clone());
                }
            }
            if descendants.is_empty() {
                Type::named(owner)
            } else {
                Type::union(descendants)
            }
        };
        self.instance_self_type_cache
            .borrow_mut()
            .insert(owner.to_owned(), type_.clone());
        type_
    }

    pub(super) fn is_concern_class_methods_module(&self, owner: &str) -> bool {
        let Some(concern_owner) = owner.strip_suffix("::ClassMethods") else {
            return false;
        };
        self.declarations
            .classes
            .get(concern_owner)
            .is_some_and(|info| {
                info.extends
                    .iter()
                    .any(|extension| extension == "ActiveSupport::Concern")
            })
    }

    pub(super) fn attached_class_type(&self, receiver_type: Option<&Type>) -> Type {
        let Some(receiver_type) = receiver_type else {
            return Type::AttachedClass;
        };
        if let Some(instance) = Self::class_object_instance_type(receiver_type) {
            return instance;
        }
        match receiver_type {
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.attached_class_type(Some(member))),
            ),
            Type::Intersection(members) => members
                .iter()
                .find_map(|member| self.attached_class_member_type(member))
                .unwrap_or_else(|| Self::receiver_instance_type(receiver_type)),
            Type::Named(name, arguments) => self
                .declarations
                .classes
                .get(name)
                .and_then(|info| info.attached_class_member)
                .and_then(|index| arguments.get(index).cloned())
                .unwrap_or_else(|| Self::receiver_instance_type(receiver_type)),
            _ => Self::receiver_instance_type(receiver_type),
        }
    }

    pub(super) fn attached_class_member_type(&self, receiver_type: &Type) -> Option<Type> {
        if let Some(instance) = Self::class_object_instance_type(receiver_type) {
            return Some(instance);
        }
        let Type::Named(name, arguments) = receiver_type else {
            return None;
        };
        let index = self.declarations.classes.get(name)?.attached_class_member?;
        arguments.get(index).cloned()
    }

    pub(super) fn substitute_instance_type(
        type_: &Type,
        receiver_type: Option<&Type>,
        attached_class: &Type,
    ) -> Type {
        match type_ {
            Type::Named(name, arguments) if name == "instance" && arguments.is_empty() => {
                receiver_type.map_or_else(|| type_.clone(), Self::receiver_instance_type)
            }
            Type::AttachedClass | Type::AttachedClassOf(_) => attached_class.clone(),
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| {
                        Self::substitute_instance_type(argument, receiver_type, attached_class)
                    })
                    .collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(Self::substitute_instance_type(
                element,
                receiver_type,
                attached_class,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(Self::substitute_instance_type(
                    key,
                    receiver_type,
                    attached_class,
                )),
                Box::new(Self::substitute_instance_type(
                    value,
                    receiver_type,
                    attached_class,
                )),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        Self::substitute_instance_type(element, receiver_type, attached_class)
                    })
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| {
                        Self::substitute_instance_type(parameter, receiver_type, attached_class)
                    })
                    .collect(),
                Box::new(Self::substitute_instance_type(
                    result,
                    receiver_type,
                    attached_class,
                )),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(Self::substitute_instance_type(
                    receiver,
                    receiver_type,
                    attached_class,
                )),
                parameters: parameters
                    .iter()
                    .map(|parameter| {
                        Self::substitute_instance_type(parameter, receiver_type, attached_class)
                    })
                    .collect(),
                result: Box::new(Self::substitute_instance_type(
                    result,
                    receiver_type,
                    attached_class,
                )),
            },
            Type::Union(members) => Type::union(members.iter().map(|member| {
                Self::substitute_instance_type(member, receiver_type, attached_class)
            })),
            Type::Intersection(members) => Type::intersection(members.iter().map(|member| {
                Self::substitute_instance_type(member, receiver_type, attached_class)
            })),
            other => other.clone(),
        }
    }

    pub(super) fn contains_type_parameter(type_: &Type, names: &BTreeSet<String>) -> bool {
        match type_ {
            Type::TypeVar(name) => names.contains(name),
            Type::Named(_, arguments) => arguments
                .iter()
                .any(|argument| Self::contains_type_parameter(argument, names)),
            Type::Array(element) => Self::contains_type_parameter(element, names),
            Type::Hash(key, value) => {
                Self::contains_type_parameter(key, names)
                    || Self::contains_type_parameter(value, names)
            }
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| Self::contains_type_parameter(element, names)),
            Type::Proc(parameters, result) => {
                parameters
                    .iter()
                    .any(|parameter| Self::contains_type_parameter(parameter, names))
                    || Self::contains_type_parameter(result, names)
            }
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => {
                Self::contains_type_parameter(receiver, names)
                    || parameters
                        .iter()
                        .any(|parameter| Self::contains_type_parameter(parameter, names))
                    || Self::contains_type_parameter(result, names)
            }
            Type::Union(members) | Type::Intersection(members) => members
                .iter()
                .any(|member| Self::contains_type_parameter(member, names)),
            _ => false,
        }
    }

    pub(super) fn infer_type_parameter_bindings(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
        block_return_type: Option<&Type>,
    ) -> BTreeMap<String, Type> {
        let names = signature
            .type_parameters
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut bindings = BTreeMap::new();
        if names.is_empty() {
            return bindings;
        }

        let positional_types = if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        for (index, actual) in positional_types.iter().enumerate() {
            if let Some(expected) = signature.positional_type(index, positional_types.len()) {
                self.collect_type_parameter_binding(expected, actual, &names, &mut bindings);
            }
        }
        // A call to a generic rest-argument constructor with no arguments
        // still has a precise element type: there are no elements, so the
        // result is parameterized by bottom.  Leaving the type variable as
        // `U` makes an empty `Set[]` fail when passed to `Set[String]`, even
        // though the set is safely covariant for every possible element type.
        if signature.accepts_rest
            && signature.rest_index == Some(0)
            && positional_types.is_empty()
            && arguments.dynamic_positional_splat_types.is_empty()
            && !arguments.forwards_arguments
        {
            if let Some(expected) = signature.params.first() {
                for name in &names {
                    if Self::contains_type_parameter(expected, &BTreeSet::from([name.clone()])) {
                        bindings.entry(name.clone()).or_insert(Type::Never);
                    }
                }
            }
        }
        if signature.accepts_rest && signature.rest_index == Some(0) {
            if let Some(expected) = signature.params.first() {
                for splat_type in &arguments.dynamic_positional_splat_types {
                    if let Type::Array(element) = splat_type {
                        self.collect_type_parameter_binding(
                            expected,
                            &element,
                            &names,
                            &mut bindings,
                        );
                    }
                }
            }
        }
        if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            for argument in &arguments.keyword_arguments {
                if let Some(expected) = signature.keywords.get(&argument.name) {
                    self.collect_type_parameter_binding(
                        &expected.type_,
                        &argument.type_,
                        &names,
                        &mut bindings,
                    );
                }
            }
        }
        if let Some(block) = signature.block.as_ref().and_then(optional_proc_type) {
            if let (Some((_, expected_return)), Some(actual_return)) =
                (proc_parts(&block), block_return_type)
            {
                self.collect_type_parameter_binding(
                    expected_return,
                    actual_return,
                    &names,
                    &mut bindings,
                );
            }
        }
        bindings
    }

    pub(super) fn collect_type_parameter_binding(
        &self,
        expected: &Type,
        actual: &Type,
        names: &BTreeSet<String>,
        bindings: &mut BTreeMap<String, Type>,
    ) {
        if actual.is_any() {
            for name in names {
                let name_set = BTreeSet::from([name.clone()]);
                if Self::contains_type_parameter(expected, &name_set) {
                    bindings.entry(name.clone()).or_insert(Type::Any);
                }
            }
            return;
        }
        match expected {
            Type::TypeVar(name) if names.contains(name) => {
                bindings
                    .entry(name.clone())
                    .and_modify(|current| *current = current.join(actual))
                    .or_insert_with(|| actual.clone());
            }
            Type::Union(members) => {
                let fixed_match = members.iter().any(|member| {
                    !Self::contains_type_parameter(member, names)
                        && self.is_assignable(actual, member)
                });
                if !fixed_match {
                    for member in members {
                        if Self::contains_type_parameter(member, names) {
                            self.collect_type_parameter_binding(member, actual, names, bindings);
                        }
                    }
                }
            }
            Type::Intersection(members) => {
                for member in members {
                    self.collect_type_parameter_binding(member, actual, names, bindings);
                }
            }
            Type::Array(expected) => {
                if let Type::Array(actual) = actual {
                    self.collect_type_parameter_binding(expected, actual, names, bindings);
                }
            }
            Type::Hash(expected_key, expected_value) => {
                if let Type::Hash(actual_key, actual_value) = actual {
                    self.collect_type_parameter_binding(expected_key, actual_key, names, bindings);
                    self.collect_type_parameter_binding(
                        expected_value,
                        actual_value,
                        names,
                        bindings,
                    );
                }
            }
            Type::Tuple(expected_elements) => match actual {
                Type::Tuple(actual_elements) => {
                    for (expected, actual) in expected_elements.iter().zip(actual_elements) {
                        self.collect_type_parameter_binding(expected, actual, names, bindings);
                    }
                }
                Type::Array(actual_element) => {
                    for expected in expected_elements {
                        self.collect_type_parameter_binding(
                            expected,
                            actual_element,
                            names,
                            bindings,
                        );
                    }
                }
                _ => {}
            },
            Type::Proc(expected_parameters, expected_result)
            | Type::BoundProc {
                parameters: expected_parameters,
                result: expected_result,
                ..
            } => {
                if let Some((actual_parameters, actual_result)) = proc_parts(actual) {
                    for (expected, actual) in expected_parameters.iter().zip(actual_parameters) {
                        self.collect_type_parameter_binding(expected, actual, names, bindings);
                    }
                    self.collect_type_parameter_binding(
                        expected_result,
                        actual_result,
                        names,
                        bindings,
                    );
                }
            }
            Type::Named(expected_name, expected_arguments) => {
                if expected_arguments.len() == 1 && name_matches(expected_name, "Enumerable") {
                    let element = match actual {
                        Type::Array(element) => Some((**element).clone()),
                        Type::Tuple(elements) => Some(Type::union(elements.iter().cloned())),
                        Type::Hash(key, value) => {
                            Some(Type::Tuple(vec![(**key).clone(), (**value).clone()]))
                        }
                        Type::Named(_, _) => {
                            self.generic_member_binding("Enumerable::Elem", Some(actual))
                        }
                        _ => None,
                    };
                    if let Some(element) = element {
                        self.collect_type_parameter_binding(
                            &expected_arguments[0],
                            &element,
                            names,
                            bindings,
                        );
                        return;
                    }
                }
                if let Type::Named(actual_name, actual_arguments) = actual {
                    if name_matches(expected_name, actual_name)
                        || name_matches(actual_name, expected_name)
                    {
                        for (expected, actual) in expected_arguments.iter().zip(actual_arguments) {
                            self.collect_type_parameter_binding(expected, actual, names, bindings);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    pub(super) fn substitute_type_parameters(
        type_: &Type,
        bindings: &BTreeMap<String, Type>,
        names: &BTreeSet<String>,
    ) -> Type {
        match type_ {
            Type::TypeVar(name) if names.contains(name) => {
                bindings.get(name).cloned().unwrap_or_else(|| type_.clone())
            }
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| Self::substitute_type_parameters(argument, bindings, names))
                    .collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(Self::substitute_type_parameters(
                element, bindings, names,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(Self::substitute_type_parameters(key, bindings, names)),
                Box::new(Self::substitute_type_parameters(value, bindings, names)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| Self::substitute_type_parameters(element, bindings, names))
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| Self::substitute_type_parameters(parameter, bindings, names))
                    .collect(),
                Box::new(Self::substitute_type_parameters(result, bindings, names)),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(Self::substitute_type_parameters(receiver, bindings, names)),
                parameters: parameters
                    .iter()
                    .map(|parameter| Self::substitute_type_parameters(parameter, bindings, names))
                    .collect(),
                result: Box::new(Self::substitute_type_parameters(result, bindings, names)),
            },
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| Self::substitute_type_parameters(member, bindings, names)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| Self::substitute_type_parameters(member, bindings, names)),
            ),
            other => other.clone(),
        }
    }

    pub(super) fn generic_member_binding(
        &self,
        name: &str,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        let receiver_type = receiver_type.map(Self::receiver_instance_type)?;
        if let Type::Union(members) = &receiver_type {
            let mut bindings = members
                .iter()
                .filter_map(|member| self.generic_member_binding(name, Some(member)));
            let first = bindings.next()?;
            return Some(bindings.fold(first, |current, member| current.join(&member)));
        }
        if name == "Enumerable::Elem" {
            match &receiver_type {
                Type::Array(element) => return Some(element.as_ref().clone()),
                Type::Hash(key, value) => {
                    return Some(Type::Tuple(vec![
                        key.as_ref().clone(),
                        value.as_ref().clone(),
                    ]))
                }
                Type::Tuple(elements) => return Some(Type::union(elements.iter().cloned())),
                Type::Named(owner, arguments) if name_matches(owner, "Enumerable") => {
                    return arguments.first().cloned();
                }
                Type::Named(owner, arguments) if name_matches(owner, "Array") => {
                    return arguments.first().cloned();
                }
                Type::Named(owner, arguments)
                    if name_matches(owner, "Hash") && arguments.len() == 2 =>
                {
                    return Some(Type::Tuple(arguments.clone()));
                }
                _ => {}
            }
        }
        let (receiver_owner, arguments) = match receiver_type {
            Type::Named(receiver_owner, arguments) => (receiver_owner.clone(), arguments.clone()),
            Type::Array(element) => ("Array".to_owned(), vec![(*element).clone()]),
            Type::Hash(key, value) => ("Hash".to_owned(), vec![(*key).clone(), (*value).clone()]),
            _ => return None,
        };
        let (declared_owner, member_name) = name.rsplit_once("::")?;
        let info = self.declarations.classes.get(declared_owner)?;
        let related = receiver_owner.as_str() == declared_owner
            || self
                .declarations
                .classes
                .get(&receiver_owner)
                .is_some_and(|receiver_info| {
                    receiver_info
                        .includes
                        .iter()
                        .any(|owner| owner == declared_owner)
                        || receiver_info
                            .prepends
                            .iter()
                            .any(|owner| owner == declared_owner)
                        || receiver_info
                            .extends
                            .iter()
                            .any(|owner| owner == declared_owner)
                })
            || self.nominal_subtype(&receiver_owner, declared_owner);
        if !related {
            return None;
        }
        let member = self
            .declarations
            .classes
            .get(&receiver_owner)
            .and_then(|receiver_info| receiver_info.type_members.get(member_name))
            .or_else(|| info.type_members.get(member_name))?;
        if let Some(fixed) = &member.fixed {
            return Some(self.resolve_type_names(fixed, Some(declared_owner)));
        }
        Some(arguments.get(member.index).cloned().unwrap_or(Type::Any))
    }

    pub(super) fn is_open_generic_member(&self, name: &str, receiver_type: Option<&Type>) -> bool {
        let Some((declared_owner, member_name)) = name.rsplit_once("::") else {
            return false;
        };
        self.declarations
            .classes
            .get(declared_owner)
            .and_then(|info| info.type_members.get(member_name))
            .is_some_and(|member| {
                member.fixed.is_none()
                    && self
                        .generic_member_binding(name, receiver_type)
                        .is_some_and(|type_| type_.is_any())
            })
    }

    pub(super) fn contains_open_generic_member(
        &self,
        type_: &Type,
        receiver_type: Option<&Type>,
    ) -> bool {
        match type_ {
            Type::TypeVar(name) => self.is_open_generic_member(name, receiver_type),
            Type::Named(_, arguments) => arguments
                .iter()
                .any(|argument| self.contains_open_generic_member(argument, receiver_type)),
            Type::Array(element) => self.contains_open_generic_member(element, receiver_type),
            Type::Hash(key, value) => {
                self.contains_open_generic_member(key, receiver_type)
                    || self.contains_open_generic_member(value, receiver_type)
            }
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| self.contains_open_generic_member(element, receiver_type)),
            Type::Proc(parameters, result) => {
                parameters
                    .iter()
                    .any(|parameter| self.contains_open_generic_member(parameter, receiver_type))
                    || self.contains_open_generic_member(result, receiver_type)
            }
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => {
                self.contains_open_generic_member(receiver, receiver_type)
                    || parameters.iter().any(|parameter| {
                        self.contains_open_generic_member(parameter, receiver_type)
                    })
                    || self.contains_open_generic_member(result, receiver_type)
            }
            Type::Union(members) | Type::Intersection(members) => members
                .iter()
                .any(|member| self.contains_open_generic_member(member, receiver_type)),
            _ => false,
        }
    }

    pub(super) fn collect_generic_member_binding(
        &self,
        expected: &Type,
        actual: &Type,
        receiver_type: Option<&Type>,
        bindings: &mut BTreeMap<String, Type>,
    ) {
        match expected {
            Type::TypeVar(name)
                if self.is_open_generic_member(name, receiver_type) && !actual.is_any() =>
            {
                bindings
                    .entry(name.clone())
                    .and_modify(|current| *current = current.join(actual))
                    .or_insert_with(|| actual.clone());
            }
            Type::Union(members) => {
                let fixed_match = members.iter().any(|member| {
                    !self.contains_open_generic_member(member, receiver_type)
                        && self.is_assignable(actual, member)
                });
                if !fixed_match {
                    for member in members {
                        if self.contains_open_generic_member(member, receiver_type) {
                            self.collect_generic_member_binding(
                                member,
                                actual,
                                receiver_type,
                                bindings,
                            );
                        }
                    }
                }
            }
            Type::Intersection(members) => {
                for member in members {
                    self.collect_generic_member_binding(member, actual, receiver_type, bindings);
                }
            }
            Type::Array(expected) => {
                if let Type::Array(actual) = actual {
                    self.collect_generic_member_binding(expected, actual, receiver_type, bindings);
                }
            }
            Type::Hash(expected_key, expected_value) => {
                if let Type::Hash(actual_key, actual_value) = actual {
                    self.collect_generic_member_binding(
                        expected_key,
                        actual_key,
                        receiver_type,
                        bindings,
                    );
                    self.collect_generic_member_binding(
                        expected_value,
                        actual_value,
                        receiver_type,
                        bindings,
                    );
                }
            }
            Type::Tuple(expected_elements) => {
                if let Type::Tuple(actual_elements) = actual {
                    for (expected, actual) in expected_elements.iter().zip(actual_elements) {
                        self.collect_generic_member_binding(
                            expected,
                            actual,
                            receiver_type,
                            bindings,
                        );
                    }
                }
            }
            Type::Proc(expected_parameters, expected_result)
            | Type::BoundProc {
                parameters: expected_parameters,
                result: expected_result,
                ..
            } => {
                if let Some((actual_parameters, actual_result)) = proc_parts(actual) {
                    for (expected, actual) in expected_parameters.iter().zip(actual_parameters) {
                        self.collect_generic_member_binding(
                            expected,
                            actual,
                            receiver_type,
                            bindings,
                        );
                    }
                    self.collect_generic_member_binding(
                        expected_result,
                        actual_result,
                        receiver_type,
                        bindings,
                    );
                }
            }
            Type::Named(expected_name, expected_arguments) => {
                if let Type::Named(actual_name, actual_arguments) = actual {
                    if name_matches(expected_name, actual_name)
                        || name_matches(actual_name, expected_name)
                    {
                        for (expected, actual) in expected_arguments.iter().zip(actual_arguments) {
                            self.collect_generic_member_binding(
                                expected,
                                actual,
                                receiver_type,
                                bindings,
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }

    pub(super) fn infer_generic_member_bindings(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
        receiver_type: Option<&Type>,
    ) -> BTreeMap<String, Type> {
        let mut bindings = BTreeMap::new();
        let positional_types = if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        for (actual, expected) in positional_types.iter().zip(&signature.params) {
            self.collect_generic_member_binding(expected, actual, receiver_type, &mut bindings);
        }
        if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            for argument in &arguments.keyword_arguments {
                if let Some(expected) = signature.keywords.get(&argument.name) {
                    self.collect_generic_member_binding(
                        &expected.type_,
                        &argument.type_,
                        receiver_type,
                        &mut bindings,
                    );
                }
            }
        }
        bindings
    }

    pub(super) fn substitute_generic_members(
        &self,
        type_: &Type,
        receiver_type: Option<&Type>,
        bindings: &BTreeMap<String, Type>,
    ) -> Type {
        match type_ {
            Type::TypeVar(name) => bindings
                .get(name)
                .cloned()
                .or_else(|| self.generic_member_binding(name, receiver_type))
                .unwrap_or_else(|| type_.clone()),
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| {
                        self.substitute_generic_members(argument, receiver_type, bindings)
                    })
                    .collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(self.substitute_generic_members(
                element,
                receiver_type,
                bindings,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(self.substitute_generic_members(key, receiver_type, bindings)),
                Box::new(self.substitute_generic_members(value, receiver_type, bindings)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        self.substitute_generic_members(element, receiver_type, bindings)
                    })
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| {
                        self.substitute_generic_members(parameter, receiver_type, bindings)
                    })
                    .collect(),
                Box::new(self.substitute_generic_members(result, receiver_type, bindings)),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(self.substitute_generic_members(
                    receiver,
                    receiver_type,
                    bindings,
                )),
                parameters: parameters
                    .iter()
                    .map(|parameter| {
                        self.substitute_generic_members(parameter, receiver_type, bindings)
                    })
                    .collect(),
                result: Box::new(self.substitute_generic_members(result, receiver_type, bindings)),
            },
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.substitute_generic_members(member, receiver_type, bindings)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| self.substitute_generic_members(member, receiver_type, bindings)),
            ),
            other => other.clone(),
        }
    }

    pub(super) fn substitute_signature_type(
        &self,
        type_: &Type,
        receiver_type: Option<&Type>,
        bindings: &BTreeMap<String, Type>,
        type_parameters: &[String],
    ) -> Type {
        let names = type_parameters.iter().cloned().collect::<BTreeSet<_>>();
        let attached_class_context = self
            .substitution_context
            .as_ref()
            .filter(|context| context.singleton)
            .and_then(|context| context.owner.as_deref())
            .filter(|owner| {
                receiver_type
                    .and_then(Self::class_object_owner)
                    .is_some_and(|receiver_owner| receiver_owner == *owner)
            });
        let attached_class = match (
            attached_class_context,
            self.substitution_context
                .as_ref()
                .map(|context| context.name.as_str()),
        ) {
            (Some(owner), Some("<class-body>" | "<singleton-body>")) => Type::named(owner),
            (Some(owner), _) => Type::AttachedClassOf(owner.to_owned()),
            (None, _) => self.attached_class_type(receiver_type),
        };
        if let Type::BoundProc {
            receiver,
            parameters,
            result,
        } = type_
        {
            let bound_receiver = if matches!(receiver.as_ref(), Type::Named(name, args) if name == "instance" && args.is_empty())
                && receiver_type.is_some()
            {
                let receiver_type = receiver_type.expect("receiver type is present");
                let preserves_class_object_self = self
                    .substitution_context
                    .as_ref()
                    .is_some_and(|context| context.singleton);
                if Self::class_object_instance_type(receiver_type).is_some()
                    && !preserves_class_object_self
                {
                    Self::class_object_instance_type(receiver_type)
                        .expect("class object instance type is present")
                } else {
                    receiver_type.clone()
                }
            } else {
                self.substitute_signature_type(receiver, receiver_type, bindings, type_parameters)
            };
            return Type::BoundProc {
                receiver: Box::new(bound_receiver),
                parameters: parameters
                    .iter()
                    .map(|parameter| {
                        self.substitute_signature_type(
                            parameter,
                            receiver_type,
                            bindings,
                            type_parameters,
                        )
                    })
                    .collect(),
                result: Box::new(self.substitute_signature_type(
                    result,
                    receiver_type,
                    bindings,
                    type_parameters,
                )),
            };
        }
        let type_ = Self::substitute_instance_type(type_, receiver_type, &attached_class);
        let type_ = self.substitute_generic_members(&type_, receiver_type, bindings);
        Self::substitute_type_parameters(&type_, bindings, &names)
    }

    pub(super) fn substitute_method_signature(
        &self,
        signature: &MethodSig,
        receiver_type: Option<&Type>,
    ) -> MethodSig {
        let bindings = BTreeMap::new();
        let mut result = signature.clone();
        result.params = signature
            .params
            .iter()
            .map(|type_| {
                self.substitute_signature_type(
                    type_,
                    receiver_type,
                    &bindings,
                    &signature.type_parameters,
                )
            })
            .collect();
        result.return_type = self.substitute_signature_type(
            &signature.return_type,
            receiver_type,
            &bindings,
            &signature.type_parameters,
        );
        result.keywords = signature
            .keywords
            .iter()
            .map(|(name, parameter)| {
                (
                    name.clone(),
                    signature::KeywordParam {
                        type_: self.substitute_signature_type(
                            &parameter.type_,
                            receiver_type,
                            &bindings,
                            &signature.type_parameters,
                        ),
                        required: parameter.required,
                    },
                )
            })
            .collect();
        result.block = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                receiver_type,
                &bindings,
                &signature.type_parameters,
            )
        });
        result
    }

    pub(super) fn looks_like_class_name(name: &str) -> bool {
        let tail = name.rsplit_once("::").map_or(name, |(_, tail)| tail);
        tail.chars()
            .next()
            .is_some_and(|character| character.is_ascii_uppercase())
            && tail.chars().any(|character| character.is_ascii_lowercase())
    }
}
