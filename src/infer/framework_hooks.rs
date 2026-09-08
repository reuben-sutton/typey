//! Framework callback receiver bindings.
//!
//! These rules model runtime callback receivers that are not represented by
//! generated RBIs. They are intentionally isolated from generic dispatch and
//! remain available to both recursive and owned callback inference.

use super::*;

impl<'src> Analyzer<'src> {
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
        binds_to_instance
            .then(|| receiver_type.and_then(Self::class_object_instance_type))
            .flatten()
    }
}
