use super::{
    name_matches, prism, proc_parts, AccessorKind, Analyzer, CallSite, Environment, MethodKey,
};
use crate::signature::{self, MethodSig};
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeSet;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_dynamic_method_body(
        &mut self,
        name: &str,
        block: &Node<'_>,
        environment: &mut Environment,
    ) {
        let receiver = environment.method_key.as_ref().and_then(|current| {
            if name == "define_method" {
                let class_body_context = matches!(
                    current.name.as_str(),
                    "<class-body>" | "<module-body>" | "<bound-block>"
                );
                if class_body_context {
                    return Self::class_object_instance_type(&environment.self_type);
                }
                None
            } else {
                // `define_singleton_method` executes with the receiver as
                // `self`, so a statically known class object is already
                // the correct bound receiver.
                (!environment.self_type.is_any()).then(|| environment.self_type.clone())
            }
        });
        if let Some(receiver) = receiver {
            let _ = self.eval_bound_block_node(block, &[Type::Any], &receiver, environment);
            return;
        }

        // A module's class methods can call `define_method` for a class that
        // will only be known when the module is extended. Traverse the body
        // with an unknown receiver so sends remain visible without inventing
        // missing-method diagnostics for the module object.
        let previous_self = environment.self_type.clone();
        let previous_method = environment.method_key.clone();
        environment.self_type = Type::Any;
        environment.method_key = None;
        let _ = self.eval_block_node(block, &[Type::Any], environment);
        environment.self_type = previous_self;
        environment.method_key = previous_method;
    }

    pub(super) fn eval_dynamic_eval_call(
        &mut self,
        name: &str,
        receiver: &Type,
        block: Option<&Node<'_>>,
        environment: &mut Environment,
    ) -> Option<Type> {
        if !matches!(
            name,
            "class_eval" | "module_eval" | "class_exec" | "instance_eval"
        ) {
            return None;
        }
        if !matches!(name, "instance_eval")
            && !receiver.is_any()
            && Self::class_object_instance_type(receiver).is_none()
        {
            return None;
        }
        let Some(block) = block else {
            // String-eval has no statically available body. It is still a
            // real Ruby API, so accept it without inventing a missing-method
            // diagnostic and preserve gradual typing for its result.
            return Some(Type::Any);
        };
        Some(self.eval_bound_block_node(block, &[Type::Any], receiver, environment))
    }

    pub(super) fn dynamic_splat_element_type(type_: &Type) -> Option<Type> {
        match type_ {
            // A dynamically splatted array contributes its element type.
            Type::Array(element) => Some(element.as_ref().clone()),
            // `*nil` contributes no arguments. For a union, retain the
            // element contributed by every possible runtime shape.
            Type::Nil => Some(Type::Never),
            Type::Union(members) => {
                let mut element = Type::Never;
                for member in members {
                    element = element.join(&Self::dynamic_splat_element_type(member)?);
                }
                Some(element)
            }
            // A non-array object is passed as one argument by Ruby's splat
            // coercion. It is therefore safe to check it against the method's
            // rest parameter instead of rejecting every non-static splat.
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

    pub(super) fn eval_tsort_method(
        &mut self,
        receiver: &Type,
        name: &str,
        environment: &Environment,
        resolved_owner: Option<&str>,
    ) -> Option<Type> {
        let Type::Named(owner, _) = receiver else {
            return None;
        };
        if !matches!(
            name,
            "strongly_connected_components" | "tsort" | "tsort_each"
        ) || (!self.receiver_has_mixin(owner, "TSort")
            && !resolved_owner.is_some_and(|owner| self.nominal_names_match(owner, "TSort")))
        {
            return None;
        }

        let element = self
            .inferred_accessor_ivar_type(owner, "edges", false, environment)
            .and_then(|edges| match edges {
                Type::Hash(_, values) => Some(self.array_element_type(&values)),
                Type::Named(name, arguments)
                    if arguments.len() == 2 && name_matches(&name, "Hash") =>
                {
                    Some(self.array_element_type(&arguments[1]))
                }
                _ => None,
            })
            .unwrap_or(Type::Any);
        match name {
            "strongly_connected_components" => {
                Some(Type::Array(Box::new(Type::Array(Box::new(element)))))
            }
            "tsort" => Some(Type::Array(Box::new(element))),
            "tsort_each" => Some(Type::Nil),
            _ => None,
        }
    }

    pub(super) fn receiver_has_mixin(&self, owner: &str, mixin: &str) -> bool {
        let mut pending = vec![owner.to_owned()];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if self.nominal_names_match(&current, mixin) {
                return true;
            }
            let Some(info) = self.declarations.classes.get(&current) else {
                continue;
            };
            pending.extend(info.includes.iter().cloned());
            pending.extend(info.prepends.iter().cloned());
            pending.extend(info.extends.iter().cloned());
            if let Some(superclass) = &info.superclass {
                pending.push(superclass.clone());
            }
        }
        false
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

    pub(super) fn option_parser_option_type(&self, type_: &Type) -> Option<Type> {
        let type_ = Self::class_object_value_type(type_).unwrap_or_else(|| type_.clone());
        match type_ {
            Type::Named(name, _) if name_matches(&name, "Array") => {
                Some(Type::Array(Box::new(Type::String)))
            }
            Type::String => Some(Type::String),
            Type::Integer => Some(Type::Integer),
            Type::Float => Some(Type::Float),
            Type::True | Type::False => Some(Type::bool()),
            Type::Named(name, _) if name_matches(&name, "TrueClass") => Some(Type::bool()),
            Type::Named(name, _) if name_matches(&name, "FalseClass") => Some(Type::bool()),
            _ => None,
        }
    }

    pub(super) fn random_formatter_signature(
        &self,
        receiver_node: Option<&Node<'_>>,
        receiver_type: &Type,
        name: &str,
    ) -> Option<MethodSig> {
        if name != "alphanumeric" {
            return None;
        }
        let constant_receiver = receiver_node
            .and_then(|receiver| self.constant_reference_name(receiver))
            .map(|name| name.trim_start_matches("::").to_owned());
        let typed_receiver = Self::class_object_instance_type(receiver_type)
            .or_else(|| Some(receiver_type.clone()))
            .and_then(|receiver| Self::named_type_name(&receiver));
        let is_random_formatter_receiver = constant_receiver
            .as_deref()
            .or(typed_receiver.as_deref())
            .is_some_and(|name| matches!(name, "Random" | "SecureRandom"));
        if !is_random_formatter_receiver {
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

    pub(super) fn eval_method_call<'a, 'node>(
        &mut self,
        receiver: &Type,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        if let Type::Union(members) = receiver {
            // An optional block local is represented as `nil | Proc`.  The
            // nil member has no normal return value for `call`/`[]` (it
            // raises at runtime), so it must not erase the concrete return
            // type of the callable member during inference.
            if matches!(name, "call" | "[]")
                && members.iter().all(|member| {
                    member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
                })
            {
                let mut result = Type::Never;
                for member in members {
                    if !member.is_nil() {
                        result =
                            result.join(&self.eval_method_call(member, name, site, environment));
                    }
                }
                return if result.is_never() { Type::Any } else { result };
            }
            let mut result = Type::Never;
            for member in members {
                result = result.join(&self.eval_method_call(member, name, site, environment));
            }
            return if result.is_never() { Type::Any } else { result };
        }

        if receiver.is_never() {
            if let Some(block) = site.block {
                let _ = self.eval_block_node(block, &[Type::Any], environment);
            }
            return Type::Never;
        }

        if let Some(type_) = self.eval_tsort_method(receiver, name, environment, None) {
            return type_;
        }

        if name == "to_yaml" {
            return Type::String;
        }

        if name == "tap" {
            if let Some(block) = site.block {
                let _ = self.eval_block_node(block, std::slice::from_ref(receiver), environment);
            }
            return receiver.clone();
        }

        if name == "freeze" {
            return receiver.clone();
        }

        if matches!(name, "dup" | "clone") {
            return receiver.clone();
        }

        if name == "class" {
            return match receiver {
                Type::Any => Type::Any,
                Type::Anything => Type::Any,
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
                Type::Named(class, _) => Self::class_object_type(class),
                Type::Intersection(_)
                | Type::Union(_)
                | Type::TypeVar(_)
                | Type::AttachedClass
                | Type::AttachedClassOf(_) => Type::Any,
            };
        }

        if matches!(
            name,
            "nil?" | "is_a?" | "kind_of?" | "instance_of?" | "==" | "!=" | "equal?" | "eql?" | "!"
        ) {
            return Type::bool();
        }

        if Self::class_object_instance_type(receiver).is_some()
            && matches!(name, "<" | "<=" | ">" | ">=")
        {
            return Type::bool();
        }

        if let Some(instance) = Self::class_object_instance_type(receiver) {
            if name == "const_get" {
                let constant_name = site.argument_nodes.first().and_then(|node| {
                    node.as_string_node()
                        .map(|string| String::from_utf8_lossy(string.unescaped()).into_owned())
                        .or_else(|| {
                            node.as_symbol_node().map(|symbol| {
                                String::from_utf8_lossy(symbol.unescaped()).into_owned()
                            })
                        })
                });
                if let (Some(owner), Some(constant_name)) =
                    (Self::named_type_name(&instance), constant_name)
                {
                    let resolved = self.resolve_name(
                        &constant_name,
                        (!constant_name.starts_with("::")).then_some(owner.as_str()),
                    );
                    if self.declarations.classes.contains_key(&resolved) {
                        return Self::class_object_type(&resolved);
                    }
                    if let Some(type_) = self.declarations.constants.get(&resolved).cloned() {
                        return self.resolve_type_names(&type_, Some(&owner));
                    }
                }
                if Self::named_type_name(&instance).is_some() {
                    // A dynamically named constant can hold any Ruby object.  That
                    // is less precise than resolving a literal name, but it is
                    // still soundly an Object rather than an untyped value.
                    return Type::Object;
                }
            }
            if Self::named_type_name(&instance)
                .is_some_and(|name| name_matches(&name, "ActiveSupport::Inflector"))
            {
                if matches!(name, "classify" | "camelize" | "underscore" | "humanize") {
                    return Type::String;
                }
                if name == "inflections" {
                    return Type::named("ActiveSupport::Inflector::Inflections");
                }
            }
            if name == "dump"
                && site.argument_types.len() == 1
                && Self::named_type_name(&instance)
                    .is_some_and(|name| name_matches(&name, "Psych") || name_matches(&name, "YAML"))
            {
                return Type::String;
            }
            if matches!(name, "load" | "load_file")
                && Self::named_type_name(&instance)
                    .is_some_and(|name| name_matches(&name, "Psych") || name_matches(&name, "YAML"))
            {
                return Type::union([Type::Nil, Type::Object]);
            }
            match name {
                "===" => return Type::bool(),
                "name" => return Type::union([Type::Nil, Type::String]),
                "const_source_location" => {
                    return Type::union([
                        Type::Nil,
                        Type::Tuple(vec![Type::String, Type::Integer]),
                    ]);
                }
                "abort" | "exit" | "exit!" | "fail" | "raise"
                    if Self::named_type_name(&instance)
                        .is_some_and(|name| name_matches(&name, "Kernel")) =>
                {
                    return Type::Never;
                }
                _ => {}
            }
        }

        if matches!(name, "id" | "object_id" | "hash") {
            return Type::Integer;
        }

        if name == "[]" {
            if let Type::Named(record, _) = receiver {
                if let Some(key) = site.argument_nodes.first() {
                    if let Some(type_) = signature::parse_inline_record_field(
                        record,
                        &prism::text(self.program.source, key),
                    ) {
                        return type_;
                    }
                }
            }
        }

        match receiver {
            Type::Array(element) => self.eval_array_method(element, name, site, environment),
            Type::Tuple(elements) => {
                if site.argument_types.is_empty() {
                    match name {
                        "first" => return elements.first().cloned().unwrap_or(Type::Nil),
                        "last" => return elements.last().cloned().unwrap_or(Type::Nil),
                        _ => {}
                    }
                }
                if name == "<=>"
                    && site.argument_types.first().is_some_and(|other| {
                        self.definitely_comparable_array_tuple(elements, other)
                    })
                {
                    return Type::Integer;
                }
                let element = elements
                    .iter()
                    .fold(Type::Never, |current, element| current.join(element));
                let element = if element.is_never() {
                    Type::Any
                } else {
                    element
                };
                self.eval_array_method(&element, name, site, environment)
            }
            Type::Hash(key, value) => self.eval_hash_method(key, value, name, site, environment),
            Type::String => self.eval_string_method(name, site, environment),
            Type::Integer => self.eval_numeric_method(
                Type::Integer,
                name,
                site.argument_types,
                site.block,
                environment,
            ),
            Type::Float => self.eval_numeric_method(
                Type::Float,
                name,
                site.argument_types,
                site.block,
                environment,
            ),
            Type::True | Type::False | Type::Nil => {
                let type_ = self.eval_common_method(name);
                if type_.is_any() {
                    if let Some(block) = site.block {
                        let _ = self.eval_block_node(block, &[Type::Any], environment);
                    }
                }
                type_
            }
            Type::Symbol => match name {
                "to_sym" | "intern" => Type::Symbol,
                "name" => Type::String,
                _ => self.eval_common_method(name),
            },
            Type::Named(class, _) if name_matches(class, "ENV") => match name {
                "[]" | "fetch" | "[]=" => Type::union([Type::Nil, Type::String]),
                _ => self.eval_common_method(name),
            },
            callable @ (Type::Proc(_, _) | Type::BoundProc { .. })
                if matches!(name, "call" | "[]") =>
            {
                let (params, result) = proc_parts(callable).expect("callable variant");
                for (index, (argument, expected)) in
                    site.argument_nodes.iter().zip(params).enumerate()
                {
                    if let Some(actual) = site.argument_types.get(index) {
                        self.check_assignable(argument, actual, expected);
                    }
                }
                result.clone()
            }
            Type::Named(class, arguments) if name == "new" && name_matches(class, "Class") => {
                let instance = Self::class_object_instance_type(receiver).unwrap_or(Type::Any);
                if Self::named_type_name(&instance).is_some_and(|name| name_matches(&name, "Class"))
                {
                    site.argument_types.first().map_or_else(
                        || Self::class_object_type("Object"),
                        |argument| match argument {
                            Type::Named(name, _) if name_matches(name, "Class") => argument.clone(),
                            _ => Self::class_object_type("Object"),
                        },
                    )
                } else {
                    if Self::named_type_name(&instance)
                        .is_some_and(|name| name_matches(&name, "Hash"))
                    {
                        if let Some(block) = site.block {
                            let hash = Type::Hash(Box::new(Type::Any), Box::new(Type::Any));
                            let _ = self.eval_block_node(block, &[hash, Type::Any], environment);
                        }
                    }
                    if Self::named_type_name(&instance)
                        .is_some_and(|name| name_matches(&name, "OptionParser"))
                    {
                        if let Some(block) = site.block {
                            let _ = self.eval_block_node(
                                block,
                                std::slice::from_ref(&instance),
                                environment,
                            );
                        }
                    }
                    let _ = arguments;
                    let result = self.instantiate_generic_class(instance);
                    if self
                        .substitution_context
                        .as_ref()
                        .filter(|context| context.singleton)
                        .and_then(|context| context.owner.as_deref())
                        .is_some_and(|owner| {
                            Self::class_object_owner(receiver).as_deref() == Some(owner)
                        })
                    {
                        Self::class_object_owner(receiver).map_or(result, Type::AttachedClassOf)
                    } else {
                        result
                    }
                }
            }
            Type::Named(class, _) if name == "[]" && name_matches(class, "Class") => {
                let instance = Self::class_object_instance_type(receiver).unwrap_or(Type::Any);
                let arguments: Vec<Type> = site
                    .argument_types
                    .iter()
                    .map(|argument| {
                        Self::class_object_value_type(argument).unwrap_or_else(|| argument.clone())
                    })
                    .collect();
                match instance {
                    Type::Named(class, _) if name_matches(&class, "Array") => {
                        arguments.first().cloned().map_or_else(
                            || Type::Array(Box::new(Type::Any)),
                            |element| Type::Array(Box::new(element)),
                        )
                    }
                    Type::Named(class, _) if name_matches(&class, "Hash") => {
                        if arguments.len() == 2 {
                            Type::Hash(
                                Box::new(arguments[0].clone()),
                                Box::new(arguments[1].clone()),
                            )
                        } else {
                            Type::Hash(Box::new(Type::Any), Box::new(Type::Any))
                        }
                    }
                    Type::Named(class, _) if name_matches(&class, "Dir") => {
                        Type::Array(Box::new(Type::String))
                    }
                    Type::Named(class, _) => Type::Named(class, arguments),
                    _ => Type::Any,
                }
            }
            Type::Named(class, _)
                if name_matches(class, "YAML") || name_matches(class, "Psych") =>
            {
                match name {
                    "dump" => Type::String,
                    "load" | "load_file" => Type::union([Type::Nil, Type::Object]),
                    _ => self.eval_common_method(name),
                }
            }
            Type::Named(class, arguments) if name == "new" => {
                if self
                    .declarations
                    .classes
                    .get(class)
                    .is_some_and(|info| !info.type_members.is_empty())
                {
                    Type::Named(class.clone(), arguments.clone())
                } else {
                    Type::Named(class.clone(), Vec::new())
                }
            }
            Type::Named(class, arguments) if name_matches(class, "Set") => match name {
                "empty?" | "include?" | "member?" => Type::bool(),
                "any?" | "all?" | "none?" => {
                    if let Some(block) = site.block {
                        let element = arguments.first().cloned().unwrap_or(Type::Any);
                        let _ = self.eval_block_node(block, &[element], environment);
                    }
                    Type::bool()
                }
                "length" | "size" => Type::Integer,
                "to_a" => Type::Array(Box::new(arguments.first().cloned().unwrap_or(Type::Any))),
                "-" => Type::Named(class.clone(), arguments.clone()),
                "|" | "&" | "+" => {
                    let element = arguments.first().cloned().unwrap_or(Type::Any);
                    let other = site
                        .argument_types
                        .first()
                        .and_then(|argument| match argument {
                            Type::Named(other_class, other_arguments)
                                if name_matches(other_class, "Set") =>
                            {
                                other_arguments.first().cloned()
                            }
                            _ => None,
                        })
                        .unwrap_or(Type::Any);
                    Type::Named(class.clone(), vec![element.join(&other)])
                }
                _ => self.eval_common_method(name),
            },
            Type::Named(class, _) if name_matches(class, "OptionParser") => match name {
                "on" => {
                    if let Some(block) = site.block {
                        let option_type = site
                            .argument_types
                            .iter()
                            .skip(1)
                            .find_map(|argument| self.option_parser_option_type(argument))
                            .unwrap_or(Type::Any);
                        let _ = self.eval_block_node(block, &[option_type], environment);
                    }
                    Type::named("OptionParser")
                }
                "parse!" => Type::Array(Box::new(Type::String)),
                _ => self.eval_common_method(name),
            },
            Type::Named(class, arguments) if name_matches(class, "Enumerator") => match name {
                "map" | "collect" => {
                    if site.block.is_none() {
                        return Type::Named(class.clone(), arguments.clone());
                    }
                    let element = arguments.first().cloned().unwrap_or(Type::Any);
                    let result = site.block.map_or(Type::Any, |block| {
                        self.eval_collection_block(block, &element, environment)
                    });
                    Type::Array(Box::new(result))
                }
                _ => self.eval_common_method(name),
            },
            Type::Named(class, _)
                if name_matches(class, "Parser::Source::Map")
                    || name_matches(class, "Parser::Source::Range") =>
            {
                match name {
                    "line" | "column" | "first_line" | "first_column" | "last_line"
                    | "last_column" => Type::Integer,
                    _ => self.eval_common_method(name),
                }
            }
            Type::Named(class, _) if name_matches(class, "Parser::AST::Node") => match name {
                "location" | "loc" => Type::named("Parser::Source::Map"),
                _ => self.eval_common_method(name),
            },
            Type::Named(class, _) if name_matches(class, "Regexp") => match name {
                "match" => Type::union([Type::Nil, Type::named("MatchData")]),
                "match?" | "===" => Type::bool(),
                "=~" | "~" => Type::union([Type::Nil, Type::Integer]),
                "source" | "to_s" => Type::String,
                "options" => Type::Integer,
                "encoding" => Type::named("Encoding"),
                _ => self.eval_common_method(name),
            },
            Type::Named(class, arguments) if name_matches(class, "Range") => {
                let begin = arguments.first().cloned().unwrap_or(Type::Any);
                let end = arguments.get(1).cloned().unwrap_or(Type::Any);
                let element = begin.join(&end).without(&Type::Nil);
                let element = if element.is_never() {
                    Type::Any
                } else {
                    element
                };
                match name {
                    "begin" => begin,
                    "end" => end,
                    "exclude_end?" => Type::bool(),
                    "include?" | "cover?" | "member?" => Type::bool(),
                    "to_a" => Type::Array(Box::new(element)),
                    "each" | "step" => {
                        if site.block.is_none() {
                            Type::named("Enumerator")
                        } else {
                            if let Some(block) = site.block {
                                let _ = self.eval_block_node(
                                    block,
                                    std::slice::from_ref(&element),
                                    environment,
                                );
                            }
                            Type::Named(class.clone(), arguments.clone())
                        }
                    }
                    "first" => begin,
                    "last" => end,
                    "to_s" | "inspect" => Type::String,
                    _ => self.eval_common_method(name),
                }
            }
            Type::Named(class, arguments)
                if name == "each" && name_matches(class, "Enumerable") =>
            {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let element = arguments.first().cloned().unwrap_or(Type::Any);
                if let Some(block) = site.block {
                    let _ =
                        self.eval_block_node(block, std::slice::from_ref(&element), environment);
                }
                Type::Named(class.clone(), arguments.clone())
            }
            Type::Named(class, _) => {
                if let Some(type_) = self.struct_field_type(class, name, environment) {
                    return type_;
                }
                if let Some(type_) =
                    self.inferred_accessor_ivar_type(class, name, false, environment)
                {
                    return type_;
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::Any], environment);
                }
                self.eval_common_method(name)
            }
            Type::Any
            | Type::Anything
            | Type::Object
            | Type::TypeVar(_)
            | Type::AttachedClass
            | Type::AttachedClassOf(_) => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::Any], environment);
                }
                self.eval_common_method(name)
            }
            Type::Never => Type::Never,
            Type::Proc(_, _) | Type::BoundProc { .. } | Type::Intersection(_) | Type::Union(_) => {
                Type::Any
            }
        }
    }
}
