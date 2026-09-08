use super::{
    ivar_refinement_key, Analyzer, ClassVarKey, Environment, IvarKey, MethodKey, SharedKey,
};
use crate::prism;
use crate::signature;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeSet;

impl<'src> Analyzer<'src> {
    pub(super) fn ivar_key(&self, environment: &Environment, name: &str) -> Option<IvarKey> {
        if let Some(method) = &environment.method_key {
            return method.owner.as_ref().map(|owner| IvarKey {
                owner: owner.clone(),
                singleton: method.singleton,
                name: name.to_owned(),
            });
        }
        if let Type::Named(owner, _) = &environment.self_type {
            return Some(IvarKey {
                owner: owner.clone(),
                singleton: false,
                name: name.to_owned(),
            });
        }
        None
    }

    pub(super) fn dynamic_ivar_keys(
        &self,
        receiver_node: Option<&Node<'_>>,
        receiver_type: &Type,
        environment: &Environment,
        name: &str,
    ) -> Vec<IvarKey> {
        if receiver_node.is_none()
            || receiver_node.is_some_and(|node| node.as_self_node().is_some())
        {
            return self.ivar_key(environment, name).into_iter().collect();
        }
        if let Type::Union(members) = receiver_type {
            return members
                .iter()
                .flat_map(|member| self.dynamic_ivar_keys(receiver_node, member, environment, name))
                .collect();
        }
        if let Some(instance) = Self::class_object_instance_type(receiver_type) {
            let instances = match instance {
                Type::Union(members) | Type::Intersection(members) => members,
                instance => vec![instance],
            };
            return instances
                .into_iter()
                .filter_map(|instance| {
                    Self::named_type_name(&instance).map(|owner| IvarKey {
                        owner,
                        // A class/module object is itself the object whose
                        // instance variable is being changed. Keep this
                        // distinct from variables on instances of that class.
                        singleton: true,
                        name: name.to_owned(),
                    })
                })
                .collect();
        }
        Self::named_type_name(receiver_type)
            .map(|owner| IvarKey {
                owner,
                singleton: false,
                name: name.to_owned(),
            })
            .into_iter()
            .collect()
    }

    pub(super) fn begin_method_evaluation(&mut self, method: &MethodKey) {
        let Some(shared_keys) = self.fixpoint.method_shared_reads.remove(method) else {
            return;
        };
        for shared_key in shared_keys {
            let empty = self
                .fixpoint
                .shared_readers
                .get_mut(&shared_key)
                .is_some_and(|readers| {
                    readers.remove(method);
                    readers.is_empty()
                });
            if empty {
                self.fixpoint.shared_readers.remove(&shared_key);
            }
        }
    }

    pub(super) fn record_shared_read(&mut self, key: SharedKey, environment: &Environment) {
        let Some(method) = environment.method_key.as_ref() else {
            return;
        };
        if !self.declarations.methods.contains_key(method) {
            return;
        }
        self.fixpoint
            .method_shared_reads
            .entry(method.clone())
            .or_default()
            .insert(key.clone());
        self.fixpoint
            .shared_readers
            .entry(key)
            .or_default()
            .insert(method.clone());
    }

    pub(super) fn observe_ivar(
        &mut self,
        environment: &Environment,
        name: String,
        actual: &Type,
        provisional: bool,
    ) {
        let Some(key) = self.ivar_key(environment, &name) else {
            return;
        };
        // A provisional `Any` write means the assigned expression has not
        // been inferred yet. It must not erase a concrete value learned in a
        // previous pass; doing so makes a later concrete write restore the
        // value, causing the shared-ivar worklist to oscillate forever.
        if provisional
            && actual.is_any()
            && self
                .ivars
                .get(&key)
                .is_some_and(|current| !current.is_any())
        {
            self.provisional_ivars.remove(&key);
            return;
        }
        let next = match self.ivars.get(&key) {
            Some(current)
                if !actual.is_any()
                    && self.provisional_ivars.contains(&key)
                    && current.is_any() =>
            {
                actual.clone()
            }
            Some(current) => current.join(actual),
            None => actual.clone(),
        };
        if provisional && actual.is_any() {
            self.provisional_ivars.insert(key.clone());
        } else {
            self.provisional_ivars.remove(&key);
        }
        if self.ivars.get(&key) != Some(&next) {
            self.ivars.insert(key.clone(), next);
            self.fixpoint.changed_shared.insert(SharedKey::Ivar(key));
        }
    }

    pub(super) fn dynamic_instance_variable_name(&self, node: &Node<'_>) -> Option<String> {
        let name = node
            .as_symbol_node()
            .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
            .or_else(|| {
                node.as_string_node()
                    .map(|string| String::from_utf8_lossy(string.unescaped()).into_owned())
            })?;
        name.starts_with('@').then_some(name)
    }

    pub(super) fn observe_dynamic_ivar(&mut self, key: IvarKey, actual: &Type) {
        let next = self
            .ivars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.ivars.get(&key) != Some(&next) {
            self.ivars.insert(key.clone(), next);
            self.fixpoint.changed_shared.insert(SharedKey::Ivar(key));
        }
    }

    pub(super) fn eval_dynamic_instance_variable_call(
        &mut self,
        name: &str,
        receiver_node: Option<&Node<'_>>,
        receiver_type: &Type,
        argument_nodes: &[Node<'_>],
        argument_types: &[Type],
        environment: &Environment,
    ) -> Option<Type> {
        let ivar_name = argument_nodes
            .first()
            .and_then(|node| self.dynamic_instance_variable_name(node));
        let keys = ivar_name
            .as_deref()
            .map(|name| self.dynamic_ivar_keys(receiver_node, receiver_type, environment, name))
            .unwrap_or_default();
        match name {
            "instance_variable_set" => {
                let actual = argument_types.get(1).cloned().unwrap_or(Type::Any);
                for key in keys {
                    self.observe_dynamic_ivar(key, &actual);
                }
                Some(actual)
            }
            "instance_variable_get" => {
                if keys.is_empty() {
                    return Some(Type::Any);
                }
                let type_ = keys
                    .iter()
                    .filter_map(|key| self.ivars.get(key))
                    .fold(Type::Never, |current, type_| current.join(type_));
                Some(if type_.is_never() { Type::Nil } else { type_ })
            }
            "instance_variable_defined?" => Some(Type::bool()),
            "instance_variables" => Some(Type::Array(Box::new(Type::Symbol))),
            _ => None,
        }
    }

    pub(super) fn preserve_typed_empty_array_ivar<'node>(
        &self,
        environment: &Environment,
        name: &str,
        value: &Node<'node>,
        actual: Type,
    ) -> Type {
        if !value
            .as_array_node()
            .is_some_and(|array| array.elements().is_empty())
        {
            return actual;
        }
        let Type::Array(element) = actual else {
            return actual;
        };
        if !element.is_any() {
            return Type::Array(element);
        }
        let refinement = ivar_refinement_key(name);
        let current = if environment.contains(&refinement) {
            Some(environment.get(&refinement))
        } else {
            self.ivar_key(environment, name)
                .and_then(|key| self.ivars.get(&key).cloned())
        };
        if let Some(Type::Array(element)) = current {
            if !element.is_any() {
                return Type::Array(element);
            }
        }
        Type::Array(element)
    }

    pub(super) fn ivar_type(&mut self, environment: &Environment, name: &str) -> Type {
        let Some(key) = self.ivar_key(environment, name) else {
            return Type::Any;
        };
        let refinement = ivar_refinement_key(name);
        if environment.contains(&refinement) {
            return environment.get(&refinement);
        }
        let owner_is_module = self
            .declarations
            .classes
            .get(&key.owner)
            .is_some_and(|info| info.is_module);
        let mut pending = if owner_is_module {
            // A method declared in a module executes against the object that
            // includes or extends it. Discover those hosts once, then walk
            // each host's ordinary ancestor chain. Reversing the graph at
            // every ancestor module can jump from a shared module such as
            // Comparable into unrelated classes and leak their ivars.
            let mut reverse_pending = vec![key.owner.clone()];
            let mut reverse_visited = BTreeSet::new();
            let mut hosts = BTreeSet::new();
            while let Some(owner) = reverse_pending.pop() {
                if !reverse_visited.insert(owner.clone()) {
                    continue;
                }
                hosts.insert(owner.clone());
                for (candidate, info) in &self.declarations.classes {
                    if info.includes.contains(&owner)
                        || info.prepends.contains(&owner)
                        || info.extends.contains(&owner)
                    {
                        hosts.insert(candidate.clone());
                        if info.is_module {
                            reverse_pending.push(candidate.clone());
                        }
                    }
                }
            }
            hosts.into_iter().collect()
        } else {
            vec![key.owner.clone()]
        };
        let mut visited = BTreeSet::new();
        while let Some(owner_name) = pending.pop() {
            if !visited.insert(owner_name.clone()) {
                continue;
            }
            let candidate = IvarKey {
                owner: owner_name.clone(),
                singleton: key.singleton,
                name: key.name.clone(),
            };
            if let Some(type_) = self.ivars.get(&candidate).cloned() {
                self.record_shared_read(SharedKey::Ivar(candidate), environment);
                return type_;
            }
            if let Some(info) = self.declarations.classes.get(&owner_name) {
                // A module extended into a class runs its instance methods
                // with the class object as `self`.  Dynamic APIs such as
                // `instance_variable_set` therefore record the field under
                // the class object's singleton key, while the method's
                // source owner still gives us the ordinary instance key.
                // Check that paired key only across an `extend` edge; doing
                // this for every superclass/include would conflate class and
                // instance state.
                if info.extends.contains(&key.owner) {
                    let extended_candidate = IvarKey {
                        owner: owner_name.clone(),
                        singleton: !key.singleton,
                        name: key.name.clone(),
                    };
                    if let Some(type_) = self.ivars.get(&extended_candidate).cloned() {
                        self.record_shared_read(SharedKey::Ivar(extended_candidate), environment);
                        return type_;
                    }
                }
                pending.extend(info.includes.iter().cloned());
                pending.extend(info.prepends.iter().cloned());
                pending.extend(info.extends.iter().cloned());
                if let Some(superclass) = &info.superclass {
                    pending.push(superclass.clone());
                }
            }
        }
        // Reading an uninitialized Ruby instance variable yields nil. Keep
        // that concrete fact instead of letting an unknown ivar poison
        // `@value ||= ...` expressions with T.untyped.
        Type::Nil
    }

    pub(super) fn inferred_accessor_ivar_type(
        &mut self,
        class: &str,
        name: &str,
        singleton: bool,
        environment: &Environment,
    ) -> Option<Type> {
        let mut pending = if self
            .declarations
            .classes
            .get(class)
            .is_some_and(|info| info.is_module)
        {
            let mut reverse_pending = vec![class.to_owned()];
            let mut reverse_visited = BTreeSet::new();
            let mut hosts = BTreeSet::new();
            while let Some(owner) = reverse_pending.pop() {
                if !reverse_visited.insert(owner.clone()) {
                    continue;
                }
                hosts.insert(owner.clone());
                for (candidate, info) in &self.declarations.classes {
                    if info.includes.contains(&owner)
                        || info.prepends.contains(&owner)
                        || info.extends.contains(&owner)
                    {
                        hosts.insert(candidate.clone());
                        if info.is_module {
                            reverse_pending.push(candidate.clone());
                        }
                    }
                }
            }
            hosts.into_iter().collect::<Vec<_>>()
        } else {
            vec![class.to_owned()]
        };
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            let key = IvarKey {
                owner: current.clone(),
                singleton,
                name: format!("@{name}"),
            };
            if let Some(type_) = self.ivars.get(&key).cloned() {
                self.record_shared_read(SharedKey::Ivar(key), environment);
                return Some(type_);
            }
            if let Some(info) = self.declarations.classes.get(&current) {
                if info.extends.iter().any(|module| module == class) {
                    let extended_key = IvarKey {
                        owner: current.clone(),
                        singleton: !singleton,
                        name: format!("@{name}"),
                    };
                    if let Some(type_) = self.ivars.get(&extended_key).cloned() {
                        self.record_shared_read(SharedKey::Ivar(extended_key), environment);
                        return Some(type_);
                    }
                }
                pending.extend(info.superclass.iter().cloned());
            }
        }
        None
    }

    pub(super) fn observe_accessor_ivar(
        &mut self,
        owner: &str,
        name: &str,
        singleton: bool,
        actual: &Type,
    ) {
        let key = IvarKey {
            owner: owner.to_owned(),
            singleton,
            name: format!("@{name}"),
        };
        let next = self
            .ivars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.ivars.get(&key) != Some(&next) {
            self.ivars.insert(key.clone(), next);
            self.fixpoint.changed_shared.insert(SharedKey::Ivar(key));
        }
    }

    pub(super) fn lexical_owner(&self, environment: &Environment) -> Option<String> {
        environment
            .method_key
            .as_ref()
            .and_then(|key| key.owner.clone())
            .or_else(|| match &environment.self_type {
                Type::Named(owner, _) => Some(owner.clone()),
                _ => None,
            })
    }

    pub(super) fn constant_key(&self, environment: &Environment, name: &str) -> String {
        let name = name.trim_start_matches("::");
        if name.contains("::") {
            return name.to_owned();
        }
        self.lexical_owner(environment)
            .map(|owner| format!("{owner}::{name}"))
            .unwrap_or_else(|| name.to_owned())
    }

    pub(super) fn scoped_constant_name(&self, environment: &Environment, name: &str) -> String {
        let absolute = name.trim_start().starts_with("::");
        let name = name.trim_start_matches("::");
        if absolute || name.contains("::") {
            return name.to_owned();
        }
        self.lexical_owner(environment)
            .map_or_else(|| name.to_owned(), |owner| format!("{owner}::{name}"))
    }

    pub(super) fn struct_subclass_type<'node>(
        &mut self,
        environment: &Environment,
        value: &Node<'node>,
        constant_name: &str,
    ) -> Option<Type> {
        let call = value.as_call_node()?;
        if prism::constant_name(call.name()) != "new" {
            return None;
        }
        let receiver = call.receiver()?;
        let receiver_name = self.constant_reference_name(&receiver)?;
        if receiver_name.trim_start_matches("::") != "Struct" {
            return None;
        }
        let fields = call
            .arguments()
            .map(|arguments| {
                arguments
                    .arguments()
                    .into_iter()
                    .filter_map(|argument| {
                        argument
                            .as_symbol_node()
                            .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        if !fields.is_empty() {
            self.declarations
                .struct_fields
                .entry(self.constant_key(environment, constant_name))
                .or_insert(fields);
        }
        Some(Type::named(self.constant_key(environment, constant_name)))
    }

    pub(super) fn eval_dynamic_struct_block<'node>(
        &mut self,
        value: &Node<'node>,
        struct_type: &Type,
        environment: &mut Environment,
    ) {
        let Some(call) = value.as_call_node() else {
            return;
        };
        if prism::constant_name(call.name()) != "new"
            || call
                .receiver()
                .and_then(|receiver| self.constant_reference_name(&receiver))
                .is_none_or(|name| name.trim_start_matches("::") != "Struct")
        {
            return;
        }
        let Some(block) = call.block() else {
            return;
        };
        let Some(owner) = Self::named_type_name(struct_type) else {
            return;
        };
        let receiver = Self::class_object_type(&owner);
        let _ = self.eval_bound_block_node(&block, &[], &receiver, environment);
    }

    pub(super) fn observe_constant(
        &mut self,
        environment: &Environment,
        name: String,
        actual: &Type,
    ) {
        let key = self.constant_key(environment, &name);
        let is_new_constant = !self.declarations.constants.contains_key(&key);
        let next = self
            .declarations
            .constants
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.declarations.constants.get(&key) != Some(&next) {
            self.declarations.constants.insert(key.clone(), next);
            if is_new_constant {
                Self::add_name_suffixes(&mut self.declarations.constant_name_suffixes, &key);
            }
            self.fixpoint
                .changed_shared
                .insert(SharedKey::Constant(key));
        }
    }

    pub(super) fn constant_type(&mut self, environment: &Environment, name: &str) -> Type {
        let absolute = name.trim_start().starts_with("::");
        let name = name.trim_start_matches("::");
        let result_owner = (!absolute)
            .then(|| self.lexical_owner(environment))
            .flatten();
        let mut candidates = vec![if absolute {
            name.to_owned()
        } else {
            self.constant_key(environment, name)
        }];
        if !absolute && candidates[0] != name {
            candidates.push(name.to_owned());
        }
        if name.contains("::") {
            let suffix = format!("::{name}");
            let mut matches = self
                .declarations
                .constants
                .keys()
                .filter(|candidate| candidate.ends_with(&suffix));
            if let Some(candidate) = matches.next() {
                if matches.next().is_none() && !candidates.contains(candidate) {
                    candidates.push(candidate.clone());
                }
            }
        }
        let mut owner = result_owner.clone();
        let mut visited = BTreeSet::new();
        while let Some(current) = owner.clone() {
            if !visited.insert(current.clone()) {
                break;
            }
            let key = format!("{current}::{name}");
            if !candidates.contains(&key) {
                candidates.push(key);
            }
            owner = self
                .declarations
                .classes
                .get(&current)
                .and_then(|info| info.superclass.clone());
        }

        // A qualified constant reference such as `Color::BLUE` is still
        // resolved lexically.  Do this before the suffix-based fallback,
        // because a workspace may contain another `Color::BLUE` (for example
        // `Thor::Shell::Color::BLUE`) that makes the suffix ambiguous.
        let resolved = self.resolve_name(name, result_owner.as_deref());
        if self.declarations.constants.contains_key(&resolved) && !candidates.contains(&resolved) {
            candidates.push(resolved.clone());
        }

        let selected = candidates
            .iter()
            .position(|candidate| self.declarations.constants.contains_key(candidate));
        let read_count = selected.map_or(candidates.len(), |index| index + 1);
        for candidate in candidates.iter().take(read_count) {
            self.record_shared_read(SharedKey::Constant(candidate.clone()), environment);
        }
        if let Some(index) = selected {
            if let Some(type_) = self.declarations.constants.get(&candidates[index]) {
                return self.resolve_type_names(type_, result_owner.as_deref());
            }
        }
        if resolved != name
            || self.declarations.classes.contains_key(&resolved)
            || Self::looks_like_class_name(&resolved)
        {
            Self::class_object_type(&resolved)
        } else {
            signature::parse_type(name)
        }
    }

    pub(super) fn class_var_owner(&self, environment: &Environment) -> String {
        self.lexical_owner(environment)
            .unwrap_or_else(|| "Object".to_owned())
    }

    pub(super) fn observe_class_var(
        &mut self,
        environment: &Environment,
        name: String,
        actual: &Type,
    ) {
        let key = ClassVarKey {
            owner: self.class_var_owner(environment),
            name,
        };
        let next = self
            .class_vars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.class_vars.get(&key) != Some(&next) {
            self.class_vars.insert(key.clone(), next);
            self.fixpoint
                .changed_shared
                .insert(SharedKey::ClassVar(key));
        }
    }

    pub(super) fn class_var_type(&mut self, environment: &Environment, name: &str) -> Type {
        let mut owner = Some(self.class_var_owner(environment));
        let mut visited = BTreeSet::new();
        let mut candidates = Vec::new();
        while let Some(current) = owner {
            if !visited.insert(current.clone()) {
                break;
            }
            candidates.push(ClassVarKey {
                owner: current.clone(),
                name: name.to_owned(),
            });
            owner = self
                .declarations
                .classes
                .get(&current)
                .and_then(|info| info.superclass.clone());
        }
        let selected = candidates
            .iter()
            .position(|candidate| self.class_vars.contains_key(candidate));
        let read_count = selected.map_or(candidates.len(), |index| index + 1);
        for candidate in candidates.iter().take(read_count) {
            self.record_shared_read(SharedKey::ClassVar(candidate.clone()), environment);
        }
        if let Some(index) = selected {
            if let Some(type_) = self.class_vars.get(&candidates[index]) {
                return type_.clone();
            }
        }
        Type::Any
    }

    pub(super) fn observe_global(&mut self, name: String, actual: &Type) {
        let next = self
            .globals
            .get(&name)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.globals.get(&name) != Some(&next) {
            self.globals.insert(name.clone(), next);
            self.fixpoint.changed_shared.insert(SharedKey::Global(name));
        }
    }
}
