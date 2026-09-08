//! Intrinsic and implicit-global call semantics.
//!
//! This layer owns the built-in contracts for Sorbet's T.*
//! intrinsics and Ruby's implicit global methods.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_t_call<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        argument_nodes: &[Node<'node>],
        argument_types: &[Type],
        environment: &mut Environment,
    ) -> Type {
        let value_types = || {
            argument_types
                .iter()
                .map(|type_| Self::class_object_value_type(type_).unwrap_or_else(|| type_.clone()))
                .collect::<Vec<_>>()
        };
        match name {
            "reveal_type" => {
                if let Some(type_) = argument_types.first() {
                    if let Some(argument) = argument_nodes.first() {
                        let description = if environment
                            .method_key
                            .as_ref()
                            .is_some_and(|method| method.name == "<bound-block>")
                        {
                            match type_ {
                                Type::Named(name, arguments)
                                    if name_matches(name, "Class") && arguments.len() == 1 =>
                                {
                                    format!("T.class_of({})", arguments[0])
                                }
                                _ => type_.to_string(),
                            }
                        } else {
                            type_.to_string()
                        };
                        self.note(argument, format!("Revealed type: `{description}`"));
                    }
                    type_.clone()
                } else {
                    self.error(node, "T.reveal_type requires one argument");
                    Type::Any
                }
            }
            "let" | "cast" | "assert_type!" | "bind" => {
                let actual = argument_types.first().cloned().unwrap_or(Type::Any);
                let expected = argument_nodes.get(1).map_or(Type::Any, |argument| {
                    let type_ = self.type_from_node(argument);
                    let owner = self.lexical_owner(environment);
                    self.resolve_type_names(&type_, owner.as_deref())
                });
                let mut expected = expected;
                if name == "let"
                    && environment
                        .method_key
                        .as_ref()
                        .is_some_and(|method| method.name == "<bound-block>")
                    && argument_nodes.get(1).is_some_and(|argument| {
                        prism::text(self.source, argument).contains("T.attached_class")
                    })
                {
                    let message =
                        "`T.attached_class` may only be used in singleton methods on classes or instance methods on `has_attached_class!` modules";
                    let annotation = argument_nodes.get(1).unwrap_or(node);
                    // Sorbet reports this invalid intrinsic once while
                    // resolving the T.let annotation and once while
                    // checking the intrinsic itself.
                    self.error(annotation, message);
                    if Self::class_object_instance_type(&environment.self_type).is_none() {
                        self.error(node, message);
                    }
                    expected = Type::Any;
                }
                if name == "let" || name == "assert_type!" {
                    self.check_assignable(
                        argument_nodes.first().unwrap_or(node),
                        &actual,
                        &expected,
                    );
                }
                if name == "assert_type!" {
                    actual
                } else {
                    expected
                }
            }
            "must" => argument_types
                .first()
                .cloned()
                .unwrap_or(Type::Any)
                .without(&Type::Nil),
            "unsafe" => Type::Any,
            "attached_class" => {
                let owner = environment
                    .method_key
                    .as_ref()
                    .and_then(|key| key.owner.as_deref());
                let is_singleton = environment
                    .method_key
                    .as_ref()
                    .is_some_and(|key| key.singleton);
                let is_module = owner
                    .and_then(|owner| self.declarations.classes.get(owner))
                    .is_some_and(|info| info.is_module);
                let has_attached_class = owner
                    .and_then(|owner| self.declarations.classes.get(owner))
                    .is_some_and(|info| info.attached_class_member.is_some());
                if is_singleton && is_module {
                    self.error(
                        node,
                        "`T.attached_class` cannot be used in singleton methods on modules, because modules cannot be instantiated",
                    );
                } else if !is_singleton && is_module && !has_attached_class {
                    self.error(
                        node,
                        format!(
                            "`{}` must declare `has_attached_class!` before module instance methods can use `T.attached_class`",
                            owner.unwrap_or("the module")
                        ),
                    );
                } else if !is_singleton && !is_module {
                    self.error(
                        node,
                        "`T.attached_class` may only be used in singleton methods on classes or instance methods on `has_attached_class!` modules",
                    );
                }
                if (is_singleton && !is_module)
                    || (!is_singleton && is_module && has_attached_class)
                {
                    owner.map_or(Type::AttachedClass, |owner| {
                        Type::AttachedClassOf(owner.to_owned())
                    })
                } else {
                    Type::Any
                }
            }
            "absurd" => {
                let actual = argument_types.first().cloned().unwrap_or(Type::Any);
                if !actual.is_never() {
                    self.error(node, format!("Expected `T.noreturn`, but found `{actual}`"));
                }
                Type::Never
            }
            "nilable" => argument_types
                .first()
                .and_then(|type_| {
                    Self::class_object_value_type(type_).or_else(|| Some(type_.clone()))
                })
                .map_or(Type::Any, |type_| Type::union([Type::Nil, type_])),
            "any" => Type::union(value_types()),
            "all" => Type::intersection(value_types()),
            "noreturn" => Type::Never,
            "class_of" => {
                match argument_types.len() {
                    0 => self.error(node, "Not enough arguments"),
                    1 => {}
                    _ => self.error(node, "Too many arguments"),
                }
                argument_types
                    .first()
                    .map(|type_| {
                        Type::Named(
                            "Class".to_owned(),
                            vec![Self::class_object_value_type(type_)
                                .unwrap_or_else(|| type_.clone())],
                        )
                    })
                    .unwrap_or_else(|| Type::Named("Class".to_owned(), vec![Type::Anything]))
            }
            _ => {
                let _ = environment;
                Type::Any
            }
        }
    }

    pub(super) fn eval_global_call<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        argument_nodes: &[Node<'node>],
        argument_types: &[Type],
        block: Option<&Node<'node>>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "puts" | "print" | "p" | "pp" | "warn" => Type::Nil,
            "is_a?" | "kind_of?" | "instance_of?" => Type::bool(),
            "require" | "require_relative" | "load" => Type::bool(),
            "raise" | "fail" | "abort" | "exit" | "exit!" => Type::Never,
            "Integer" => Type::Integer,
            "Float" => Type::Float,
            "String" | "__dir__" => Type::String,
            "Symbol" => Type::Symbol,
            "Array" => self
                .global_call_type(name, argument_types)
                .unwrap_or(Type::Any),
            "Hash" => {
                if let Some(block) = block {
                    let hash = Type::Hash(Box::new(Type::Any), Box::new(Type::Any));
                    let _ = self.eval_block_node(block, &[hash, Type::Any], environment);
                }
                Type::Hash(Box::new(Type::Any), Box::new(Type::Any))
            }
            "lambda" | "proc" => Type::Proc(Vec::new(), Box::new(Type::Any)),
            "to_enum" | "enum_for" => Type::named("Enumerator"),
            "block_given?" => Type::bool(),
            "loop" => {
                if let Some(block) = block {
                    let block_type = self.eval_block_node(block, &[Type::Any], environment);
                    if block_type.is_never() {
                        Type::Never
                    } else {
                        // A block may terminate the loop with `break`; when
                        // that value cannot be recovered precisely, retain a
                        // typed top rather than turning the whole call into
                        // an unmodeled `T.untyped` send.
                        Type::Object
                    }
                } else {
                    Type::named("Enumerator")
                }
            }
            "throw" => Type::Never,
            "binding" => Type::named("Binding"),
            "gem" => Type::named("Gem::Specification"),
            "rand" => Type::Float,
            "sleep" => Type::Integer,
            "const_get" => Type::Object,
            // Sorbet's declaration DSL is intentionally executable Ruby.  It
            // is not an application method that needs a user definition, but
            // it still has to be recognized in `typed: true` files so that
            // missing-method checking does not mistake declarations for API
            // typos.
            "sig"
            | "private_class_method"
            | "has_attached_class!"
            | "type_member"
            | "type_template"
            | "mixes_in_class_methods"
            | "each"
            | "alias_method"
            | "attr_reader"
            | "attr_writer"
            | "attr_accessor"
            | "private"
            | "protected"
            | "public"
            | "module_function"
            | "autoload"
            | "private_constant"
            | "public_constant"
            | "refine" => Type::Nil,
            "include" | "prepend" => {
                if name == "include" {
                    self.observe_include_hook(node, argument_nodes, environment);
                }
                Type::Nil
            }
            "extend" => {
                self.observe_extend_hook(node, argument_nodes, environment);
                Type::Nil
            }
            "id" | "object_id" | "hash" => Type::Integer,
            // Module's dynamic method-definition APIs are available through
            // an implicit receiver while evaluating a module method that is
            // later extended onto a class.
            "define_method" | "define_singleton_method" => {
                if let Some(block) = block {
                    // The block becomes a method body at runtime.  Even when
                    // the method name is dynamic, traverse it now so sends
                    // inside the body are not silently omitted from the
                    // analysis.
                    self.eval_dynamic_method_body(name, block, environment);
                }
                Type::Symbol
            }
            _ => {
                if let Some(block) = block {
                    // Even when a global call has no modeled signature, Ruby
                    // still evaluates its block.  Traverse it with an
                    // unknown argument shape so concrete sends in the block
                    // remain visible to inference and send accounting.
                    let _ = self.eval_block_node(block, &[Type::Any], environment);
                }
                let _ = (node, argument_nodes, environment);
                Type::Any
            }
        }
    }

    /// Return the result of a global call whose contract is structural rather
    /// than an ordinary method signature.  The CFG call transfer uses this
    /// same semantic layer as the parser-facing evaluator so intrinsic calls
    /// cannot drift from their legacy behavior.
    pub(super) fn global_call_type(&self, name: &str, argument_types: &[Type]) -> Option<Type> {
        match name {
            "Array" => Some(argument_types.first().map_or_else(
                || Type::Array(Box::new(Type::Any)),
                |type_| Type::Array(Box::new(self.array_coercion_element_type(type_))),
            )),
            _ => None,
        }
    }
}
