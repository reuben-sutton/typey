//! Framework callback receiver bindings.
//!
//! These rules model runtime callback receivers that are not represented by
//! generated RBIs. They are intentionally isolated from generic dispatch and
//! remain available to both recursive and owned callback inference.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn observe_mixin_hook_owned(
        &mut self,
        site: SourceSite,
        module_name: String,
        base_type: &Type,
        environment: &mut Environment,
        extend: bool,
    ) {
        let Some(base_types) = Self::class_object_instance_types(base_type) else {
            return;
        };
        for base_type in base_types {
            let Some(base_type) = Self::named_type_name(&base_type) else {
                continue;
            };
            let info = self
                .declarations
                .classes
                .entry(base_type.clone())
                .or_default();
            let changed = if extend {
                if info.extends.contains(&module_name) {
                    false
                } else {
                    info.extends.push(module_name.clone());
                    true
                }
            } else if info.includes.contains(&module_name) {
                false
            } else {
                info.includes.push(module_name.clone());
                true
            };
            if changed {
                self.method_resolution_cache.borrow_mut().clear();
                self.instance_self_type_cache.borrow_mut().clear();
                self.schedule_method_resolution_dependents(&base_type);
                // Module-owned method bodies can use generated accessors whose
                // ivars are supplied by the eventual includer. Revisit those
                // bodies when this mixin becomes visible as well as revisiting
                // the includer's callers.
                self.schedule_method_resolution_dependents(&module_name);
                self.fixpoint.changed_methods.extend(
                    self.declarations
                        .methods
                        .keys()
                        .filter(|key| key.owner.as_deref() == Some(module_name.as_str()))
                        .cloned(),
                );
            }
            let hook = MethodKey {
                owner: Some(module_name.clone()),
                name: if extend { "extended" } else { "included" }.to_owned(),
                singleton: true,
            };
            let mut hook_arguments = CallArguments::default();
            hook_arguments
                .argument_types
                .push(Self::class_object_type(&base_type));
            hook_arguments
                .positional_types
                .push(Self::class_object_type(&base_type));
            let Some(signature) = self.observe_call(&hook, &hook_arguments, false) else {
                continue;
            };
            self.record_method_dependency(&hook, environment);
            let receiver_type = Self::class_object_type(&module_name);
            let _ = self.invoke_signature_at(
                site,
                if extend { "extended" } else { "included" },
                &signature,
                &hook_arguments,
                Some(&receiver_type),
                None,
            );
        }
    }

    /// Rails initializers are stored as callbacks and later executed with
    /// `Rails::Initializable::Initializer#run`, which uses `instance_exec` on
    /// the engine or railtie instance. The generated Rails RBI does not encode
    /// that receiver binding, so recover it from the defining extension
    /// module when checking an initializer declaration block.
    pub(super) fn rails_initializer_block_receiver(
        &self,
        key: &MethodKey,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        let owner = key.owner.as_deref()?;
        (owner == "Rails::Initializable::ClassMethods" && key.name == "initializer")
            .then(|| receiver_type.and_then(Self::class_object_instance_type))
            .flatten()
    }

    /// `Rails.application.configure` evaluates its block with the application
    /// instance as `self`. Tapioca's RBI leaves both the application factory
    /// and the callback binding untyped, but a repository normally declares a
    /// concrete subclass of `Rails::Application`. Preserve that concrete
    /// runtime receiver when checking the configuration block.
    pub(super) fn rails_application_configure_block_receiver(
        &self,
        key: &MethodKey,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        (key.name == "configure")
            .then(|| receiver_type.filter(|type_| self.is_rails_application_instance(type_)))
            .flatten()
            .cloned()
    }

    pub(super) fn is_rails_application_instance(&self, type_: &Type) -> bool {
        match type_ {
            Type::Named(name, _) => {
                self.nominal_subtype_names(nominal_name(name), "Rails::Application")
            }
            Type::Union(members) => {
                !members.is_empty()
                    && members
                        .iter()
                        .all(|member| self.is_rails_application_instance(member))
            }
            _ => false,
        }
    }

    pub(super) fn rails_application_instance_type(&self) -> Option<Type> {
        let applications = self
            .declarations
            .classes
            .iter()
            .filter(|(name, info)| {
                !info.is_module
                    && name.as_str() != "Rails::Application"
                    && self.nominal_subtype_names(nominal_name(name), "Rails::Application")
            })
            .map(|(name, _)| Type::named(name.clone()))
            .collect::<Vec<_>>();
        if !applications.is_empty() {
            return Some(Type::union(applications));
        }
        self.declarations
            .classes
            .contains_key("Rails::Application")
            .then(|| Type::named("Rails::Application"))
    }

    /// Owned contracts for Rails' two factory calls which are deliberately
    /// left open by generated RBIs. These results feed the normal receiver
    /// dispatch path, so subsequent `configure` and `draw` blocks still use
    /// their ordinary callback-binding rules.
    pub(super) fn owned_framework_call_type(
        &self,
        receiver_type: &Type,
        name: &str,
    ) -> Option<Type> {
        let receiver_name = Self::class_object_instance_type(receiver_type)
            .and_then(|instance| Self::named_type_name(&instance))
            .or_else(|| Self::named_type_name(receiver_type));
        if name == "application"
            && receiver_name
                .as_deref()
                .is_some_and(|name| name.trim_start_matches("::") == "Rails")
        {
            return self.rails_application_instance_type();
        }
        if name == "routes" && self.is_rails_application_instance(receiver_type) {
            return Some(Type::named("ActionDispatch::Routing::RouteSet"));
        }
        None
    }

    pub(super) fn rails_route_draw_block_receiver(
        &self,
        key: &MethodKey,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        (key.name == "draw")
            .then(|| {
                receiver_type.filter(|type_| match type_ {
                    Type::Named(name, _) => self.nominal_subtype_names(
                        nominal_name(name),
                        "ActionDispatch::Routing::RouteSet",
                    ),
                    _ => false,
                })
            })
            .flatten()
            .map(|_| Type::named("ActionDispatch::Routing::Mapper"))
    }

    pub(super) fn active_support_ci_block_receiver(
        &self,
        key: &MethodKey,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        (key.singleton
            && key.name == "run"
            && key.owner.as_deref() == Some("ActiveSupport::ContinuousIntegration"))
        .then(|| receiver_type.and_then(Self::class_object_instance_type))
        .flatten()
    }

    /// Active Support's test DSL is implemented by defining instance methods,
    /// but its generated RBI deliberately leaves the callback untyped. Model
    /// the runtime receiver from the extension module instead of checking the
    /// declaration block against `Class[TestCase]`.
    pub(super) fn active_support_test_block_receiver(
        &self,
        key: &MethodKey,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        let owner = key.owner.as_deref()?;
        let binds_to_instance = (owner == "ActiveSupport::Testing::Declarative"
            && key.name == "test")
            || (owner == "Minitest::Test" && key.name == "test")
            || (owner == "ActiveSupport::Testing::SetupAndTeardown::ClassMethods"
                && matches!(key.name.as_str(), "setup" | "teardown"));
        let receiver_instance = receiver_type.and_then(Self::class_object_instance_type);
        let receiver_is_test_case = receiver_instance.as_ref().is_some_and(|instance| {
            let Some(name) = Self::named_type_name(instance) else {
                return false;
            };
            self.nominal_subtype_names(&name, "Minitest::Test")
                || self.nominal_subtype_names(&name, "ActiveSupport::TestCase")
        });
        (binds_to_instance
            || (key.singleton
                && receiver_is_test_case
                && matches!(key.name.as_str(), "test" | "setup" | "teardown")))
        .then_some(receiver_instance)
        .flatten()
    }

    pub(super) fn observe_extend_hook<'node>(
        &mut self,
        node: &Node<'node>,
        argument_nodes: &[Node<'node>],
        environment: &mut Environment,
    ) {
        let Some(base_type) = Self::class_object_owner(&environment.self_type) else {
            return;
        };
        let base_type = Self::class_object_type(&base_type);
        self.observe_extend_hook_for_base(node, argument_nodes, &base_type, environment);
    }

    pub(super) fn observe_extend_hook_for_base<'node>(
        &mut self,
        node: &Node<'node>,
        argument_nodes: &[Node<'node>],
        base_type: &Type,
        environment: &mut Environment,
    ) {
        let Some(base_types) = Self::class_object_instance_types(base_type) else {
            return;
        };
        let Some(argument) = argument_nodes.first() else {
            return;
        };
        let Some(module_name) = self
            .constant_reference_name(argument)
            .map(|name| self.resolve_name(&name, self.lexical_owner(environment).as_deref()))
        else {
            return;
        };
        for base_type in base_types {
            let Some(base_type) = Self::named_type_name(&base_type) else {
                continue;
            };
            let info = self
                .declarations
                .classes
                .entry(base_type.clone())
                .or_default();
            if !info.extends.contains(&module_name) {
                info.extends.push(module_name.clone());
                self.method_resolution_cache.borrow_mut().clear();
                self.instance_self_type_cache.borrow_mut().clear();
                self.schedule_method_resolution_dependents(&base_type);
            }
            let hook = MethodKey {
                owner: Some(module_name.clone()),
                name: "extended".to_owned(),
                singleton: true,
            };
            let mut hook_arguments = CallArguments::default();
            hook_arguments
                .argument_types
                .push(Self::class_object_type(&base_type));
            hook_arguments
                .positional_types
                .push(Self::class_object_type(&base_type));
            let Some(signature) = self.observe_call(&hook, &hook_arguments, false) else {
                continue;
            };
            self.record_method_dependency(&hook, environment);
            let receiver_type = Self::class_object_type(&module_name);
            let _ = self.invoke_signature(
                node,
                "extended",
                &signature,
                &hook_arguments,
                Some(&receiver_type),
                None,
            );
        }
    }

    pub(super) fn observe_include_hook<'node>(
        &mut self,
        node: &Node<'node>,
        argument_nodes: &[Node<'node>],
        environment: &mut Environment,
    ) {
        let Some(base_type) = Self::class_object_owner(&environment.self_type) else {
            return;
        };
        let base_type = Self::class_object_type(&base_type);
        self.observe_include_hook_for_base(node, argument_nodes, &base_type, environment);
    }

    pub(super) fn observe_include_hook_for_base<'node>(
        &mut self,
        node: &Node<'node>,
        argument_nodes: &[Node<'node>],
        base_type: &Type,
        environment: &mut Environment,
    ) {
        let Some(base_types) = Self::class_object_instance_types(base_type) else {
            return;
        };
        let Some(argument) = argument_nodes.first() else {
            return;
        };
        let Some(module_name) = self
            .constant_reference_name(argument)
            .map(|name| self.resolve_name(&name, self.lexical_owner(environment).as_deref()))
        else {
            return;
        };
        for base_type in base_types {
            let Some(base_type) = Self::named_type_name(&base_type) else {
                continue;
            };
            let info = self
                .declarations
                .classes
                .entry(base_type.clone())
                .or_default();
            if !info.includes.contains(&module_name) {
                info.includes.push(module_name.clone());
                self.method_resolution_cache.borrow_mut().clear();
                self.instance_self_type_cache.borrow_mut().clear();
                self.schedule_method_resolution_dependents(&base_type);
            }
            let hook = MethodKey {
                owner: Some(module_name.clone()),
                name: "included".to_owned(),
                singleton: true,
            };
            let mut hook_arguments = CallArguments::default();
            hook_arguments
                .argument_types
                .push(Self::class_object_type(&base_type));
            hook_arguments
                .positional_types
                .push(Self::class_object_type(&base_type));
            let Some(signature) = self.observe_call(&hook, &hook_arguments, false) else {
                continue;
            };
            self.record_method_dependency(&hook, environment);
            let receiver_type = Self::class_object_type(&module_name);
            let _ = self.invoke_signature(
                node,
                "included",
                &signature,
                &hook_arguments,
                Some(&receiver_type),
                None,
            );
        }
    }
}
