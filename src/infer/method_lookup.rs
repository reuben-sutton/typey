use super::{Analyzer, CallArguments, Environment, MethodKey, SharedKey, SourceSite};
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeSet;

impl<'src> Analyzer<'src> {
    pub(super) fn record_method_dependency(&mut self, key: &MethodKey, environment: &Environment) {
        let Some(callee) = self.resolve_method_key(key) else {
            return;
        };
        let Some(caller) = environment.method_key.as_ref() else {
            return;
        };
        if self.declarations.methods.contains_key(caller) {
            self.fixpoint
                .method_callers
                .entry(callee)
                .or_default()
                .insert(caller.clone());
        }
    }

    /// Recursive inferred methods need a finite widening point. A direct
    /// recursive call otherwise substitutes the method's current return
    /// summary into itself, so `Array#map { attributes(element) }` grows an
    /// additional nested `Array[...]` on every worklist round. Recursive
    /// containers use `Object` as a finite concrete upper bound; scalar and
    /// nominal recursive edges use bottom so non-recursive branches retain
    /// their precise result without manufacturing `T.untyped`.
    pub(super) fn widen_recursive_call_return(
        &self,
        key: &MethodKey,
        type_: Type,
        environment: &Environment,
    ) -> Type {
        if !self.fixpoint.collecting_returns || type_.is_never() {
            return type_;
        }
        let Some(current) = environment.method_key.as_ref() else {
            return type_;
        };
        let Some(current) = self.resolve_method_key(current) else {
            return type_;
        };
        let Some(callee) = self.resolve_method_key(key) else {
            return type_;
        };
        if current != callee
            || self
                .declarations
                .methods
                .get(&current)
                .is_some_and(|state| state.explicit)
        {
            type_
        } else if !matches!(type_, Type::Array(_) | Type::Hash(..) | Type::Tuple(_)) {
            // A recursive call is a provisional edge while its method
            // summary is being solved. For scalar/nominal results, bottom
            // lets a concrete non-recursive path determine the method's
            // result without turning an accumulator expression such as
            // `accept(..., seed) << suffix` into an `Object#<<` error.
            Type::Never
        } else {
            // Recursive containers still need a finite concrete widening
            // point so nested results do not grow forever
            // (`[recursive_call]` becomes `Array[Object]`).
            Type::Object
        }
    }

    pub(super) fn resolve_method_key(&self, key: &MethodKey) -> Option<MethodKey> {
        if let Some(resolved) = self.method_resolution_cache.borrow().get(key) {
            return resolved.clone();
        }
        let resolved = self.resolve_method_key_inner(key, &mut BTreeSet::new());
        self.method_resolution_cache
            .borrow_mut()
            .insert(key.clone(), resolved.clone());
        resolved
    }

    pub(super) fn resolve_method_key_inner(
        &self,
        key: &MethodKey,
        visited: &mut BTreeSet<MethodKey>,
    ) -> Option<MethodKey> {
        if !visited.insert(key.clone()) {
            return None;
        }
        let mut candidates = Vec::new();
        if let Some(owner) = &key.owner {
            let owner = self.resolve_global_name(owner);
            self.append_method_candidates(
                &owner,
                &key.name,
                key.singleton,
                &mut BTreeSet::new(),
                &mut candidates,
            );
            // A class object dispatches first to the receiver's singleton
            // class, then to the instance methods of Class/Module.  The
            // receiver key only stores the former owner, so add the latter
            // lookup explicitly when a singleton call did not resolve there.
            // This is what makes APIs such as Module#const_get and
            // Module#class_eval visible on `SomeClass`, without accepting an
            // arbitrary missing singleton method.
            if key.singleton {
                self.append_method_candidates(
                    "Class",
                    &key.name,
                    false,
                    &mut BTreeSet::new(),
                    &mut candidates,
                );
            }
        } else {
            candidates.push(key.clone());
        }
        for candidate in candidates {
            if self.declarations.methods.contains_key(&candidate) {
                return Some(candidate);
            }
            if let Some(target) = self.declarations.aliases.get(&candidate) {
                if let Some(resolved) = self.resolve_method_key_inner(target, visited) {
                    return Some(resolved);
                }
            }
        }
        None
    }

    pub(super) fn append_method_candidates(
        &self,
        owner: &str,
        name: &str,
        singleton: bool,
        visited: &mut BTreeSet<String>,
        candidates: &mut Vec<MethodKey>,
    ) {
        if !visited.insert(owner.to_owned()) {
            return;
        }
        let info = self.declarations.classes.get(owner);
        if !singleton {
            if let Some(info) = info {
                for module in info.prepends.iter().rev() {
                    self.append_method_candidates(module, name, false, visited, candidates);
                }
            }
        }
        candidates.push(MethodKey {
            owner: Some(owner.to_owned()),
            name: name.to_owned(),
            singleton,
        });
        if let Some(info) = info {
            if singleton {
                if info.extend_self {
                    for module in info.prepends.iter().rev() {
                        self.append_method_candidates(module, name, false, visited, candidates);
                    }
                    candidates.push(MethodKey {
                        owner: Some(owner.to_owned()),
                        name: name.to_owned(),
                        singleton: false,
                    });
                    for ancestor in info.requires_ancestors.iter().rev() {
                        self.append_method_candidates(ancestor, name, false, visited, candidates);
                    }
                    for module in info.includes.iter().rev() {
                        self.append_method_candidates(module, name, false, visited, candidates);
                    }
                }
                for module in info.extends.iter().rev() {
                    self.append_method_candidates(module, name, false, visited, candidates);
                }
            }
            if !singleton {
                for ancestor in info.requires_ancestors.iter().rev() {
                    self.append_method_candidates(ancestor, name, false, visited, candidates);
                }
                for module in info.includes.iter().rev() {
                    self.append_method_candidates(module, name, false, visited, candidates);
                }
            }
            if let Some(superclass) = &info.superclass {
                self.append_method_candidates(superclass, name, singleton, visited, candidates);
            }
        }
    }

    pub(super) fn infer_initializer_call<'node>(
        &mut self,
        node: &Node<'node>,
        owner: &str,
        arguments: &CallArguments<'node>,
        has_block: bool,
        environment: &Environment,
    ) {
        self.infer_initializer_call_at(
            SourceSite::from_prism_span(prism::span(node)),
            owner,
            arguments,
            has_block,
            environment,
        );
    }

    pub(super) fn infer_initializer_call_at(
        &mut self,
        site: SourceSite,
        owner: &str,
        arguments: &CallArguments<'_>,
        has_block: bool,
        environment: &Environment,
    ) {
        let key = MethodKey {
            owner: Some(owner.to_owned()),
            name: "initialize".to_owned(),
            singleton: false,
        };
        self.record_method_dependency(&key, environment);
        if let Some(signature) = self.observe_call(&key, arguments, has_block) {
            let receiver_type = Type::named(owner.to_owned());
            let initializer_requires_block = self
                .resolve_method_key(&key)
                .and_then(|resolved| self.declarations.methods.get(&resolved))
                .is_some_and(|state| state.explicit);
            let previous_checking_initializer = self.checking_initializer;
            let previous_initializer_has_block = self.initializer_has_block;
            let previous_initializer_requires_block = self.initializer_requires_block;
            self.checking_initializer = true;
            self.initializer_has_block = has_block;
            self.initializer_requires_block = initializer_requires_block;
            let _ = self.invoke_signature_at(
                site,
                "initialize",
                &signature,
                arguments,
                Some(&receiver_type),
                None,
            );
            self.checking_initializer = previous_checking_initializer;
            self.initializer_has_block = previous_initializer_has_block;
            self.initializer_requires_block = previous_initializer_requires_block;
        }
    }

    pub(super) fn observe_struct_constructor(
        &mut self,
        owner: &str,
        arguments: &CallArguments<'_>,
    ) {
        let Some(fields) = self.declarations.struct_fields.get(owner).cloned() else {
            return;
        };
        let mut observations = fields
            .iter()
            .zip(&arguments.positional_types)
            .map(|(field, actual)| (field.clone(), actual.clone()))
            .collect::<Vec<_>>();
        observations.extend(arguments.keyword_arguments.iter().filter_map(|argument| {
            fields
                .iter()
                .any(|field| field == &argument.name)
                .then(|| (argument.name.clone(), argument.type_.clone()))
        }));
        for (field, actual) in observations {
            let key = (owner.to_owned(), field.clone());
            let next = self
                .declarations
                .struct_field_types
                .get(&key)
                .map_or_else(|| actual.clone(), |current| current.join(&actual));
            if self.declarations.struct_field_types.get(&key) != Some(&next) {
                self.declarations
                    .struct_field_types
                    .insert(key.clone(), next);
                self.fixpoint
                    .changed_shared
                    .insert(SharedKey::StructField(key.0, key.1));
            }
        }
    }

    pub(super) fn struct_field_type(
        &mut self,
        owner: &str,
        name: &str,
        environment: &Environment,
    ) -> Option<Type> {
        if !self
            .declarations
            .struct_fields
            .get(owner)
            .is_some_and(|fields| fields.iter().any(|field| field == name))
        {
            return None;
        }
        let key = (owner.to_owned(), name.to_owned());
        self.record_shared_read(
            SharedKey::StructField(key.0.clone(), key.1.clone()),
            environment,
        );
        Some(
            self.declarations
                .struct_field_types
                .get(&key)
                .cloned()
                .unwrap_or(Type::Any),
        )
    }

    pub(super) fn implicit_method_key(&self, name: &str, environment: &Environment) -> MethodKey {
        if let Some(current) = &environment.method_key {
            let class_object_owner = Self::class_object_owner(&environment.self_type);
            let owner = class_object_owner.clone().or_else(|| {
                Self::named_type_name(&environment.self_type).or_else(|| current.owner.clone())
            });
            MethodKey {
                owner,
                name: name.to_owned(),
                singleton: class_object_owner.is_some() || current.singleton,
            }
        } else {
            MethodKey::top_level(name)
        }
    }

    pub(super) fn receiver_method_key<'node>(
        &self,
        receiver_node: Option<&Node<'node>>,
        receiver_type: &Type,
        name: &str,
        environment: &Environment,
    ) -> Option<MethodKey> {
        let (owner, class_object) = if let Some(owner) = Self::class_object_owner(receiver_type) {
            (owner, true)
        } else if let Type::AttachedClassOf(owner) = receiver_type {
            (owner.clone(), false)
        } else if let Type::Named(owner, _) = receiver_type {
            let owner = owner
                .strip_prefix("T::")
                .filter(|bare| self.declarations.classes.contains_key(*bare))
                .map_or_else(|| owner.clone(), str::to_owned);
            (owner, false)
        } else {
            let owner = match receiver_type {
                Type::Nil => "NilClass",
                Type::True => "TrueClass",
                Type::False => "FalseClass",
                Type::Integer => "Integer",
                Type::Float => "Float",
                Type::String => "String",
                Type::Symbol => "Symbol",
                Type::Object => "Object",
                Type::Array(_) => "Array",
                Type::Tuple(_) => "Array",
                Type::Hash(_, _) => "Hash",
                Type::Any
                | Type::Anything
                | Type::Never
                | Type::Named(_, _)
                | Type::Proc(_, _)
                | Type::Intersection(_)
                | Type::Union(_)
                | Type::TypeVar(_)
                | Type::AttachedClass
                | Type::AttachedClassOf(_)
                | Type::BoundProc { .. } => return None,
            };
            (owner.to_owned(), false)
        };
        let singleton = if class_object {
            true
        } else if receiver_node.is_some_and(|node| node.as_self_node().is_some()) {
            environment
                .method_key
                .as_ref()
                .is_some_and(|key| key.singleton)
        } else {
            false
        };
        Some(MethodKey {
            owner: Some(owner),
            name: name.to_owned(),
            singleton,
        })
    }

    pub(super) fn super_method_key(&self, current: &MethodKey) -> Option<MethodKey> {
        let owner = current.owner.as_ref()?;
        let mut candidates = Vec::new();
        self.append_method_candidates(
            owner,
            &current.name,
            current.singleton,
            &mut BTreeSet::new(),
            &mut candidates,
        );
        let mut after_current = false;
        let mut visited = BTreeSet::new();
        for candidate in candidates {
            if !after_current {
                if candidate.owner.as_ref() == Some(owner) {
                    after_current = true;
                }
                continue;
            }
            if self.declarations.methods.contains_key(&candidate) {
                return Some(candidate);
            }
            if self.declarations.aliases.contains_key(&candidate) {
                if let Some(resolved) = self.resolve_method_key_inner(&candidate, &mut visited) {
                    return Some(resolved);
                }
            }
        }
        None
    }
}
