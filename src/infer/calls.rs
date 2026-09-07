use super::{
    name_matches, prism, Analyzer, CallShape, CallSite, Environment, Eval, Flow, FlowKind, Node,
    OutcomeTypes, UntypedOrigin, Visibility,
};
use crate::types::Type;

impl<'src> Analyzer<'src> {
    pub(super) fn is_open_array_append_receiver(
        &self,
        node: &Node<'_>,
        environment: &Environment,
    ) -> bool {
        if let Some(local) = node.as_local_variable_read_node() {
            return environment
                .open_array_locals
                .contains(&prism::constant_name(local.name()));
        }
        let Some(call) = node.as_call_node() else {
            return false;
        };
        matches!(
            prism::constant_name(call.name()).as_str(),
            "push" | "<<" | "prepend"
        ) && call
            .receiver()
            .is_some_and(|receiver| self.is_open_array_append_receiver(&receiver, environment))
    }

    pub(super) fn static_type_value(&self, node: &Node<'_>) -> bool {
        let Some(call) = node.as_call_node() else {
            return false;
        };
        let name = prism::constant_name(call.name());
        let arguments = call
            .arguments()
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        if name == "first"
            && call.receiver().as_ref().is_some_and(|receiver| {
                receiver.as_array_node().is_some_and(|array| {
                    !array.elements().is_empty()
                        && array
                            .elements()
                            .iter()
                            .all(|element| self.static_type_value(&element))
                })
            })
        {
            return true;
        }
        let Some(receiver) = call.receiver() else {
            return false;
        };
        let receiver_is_t = self
            .constant_reference_name(&receiver)
            .is_some_and(|name| name.trim_start_matches("::") == "T");
        let direct_type_constructor = receiver_is_t
            && match name.as_str() {
                "class_of" => arguments.len() == 1,
                "any" | "all" | "nilable" | "noreturn" | "untyped" | "self_type" | "proc"
                | "type_parameter" | "attached_class" => true,
                _ => false,
            };
        let generic_type_constructor = name == "[]"
            && self
                .constant_reference_name(&receiver)
                .is_some_and(|name| name.trim_start_matches("::").starts_with("T::"));
        if direct_type_constructor || generic_type_constructor {
            return true;
        }
        if self.static_type_value(&receiver) {
            return !matches!(
                name.as_str(),
                "new"
                    | "valid?"
                    | "recursively_valid?"
                    | "subtype_of?"
                    | "describe_obj"
                    | "error_message_for_obj"
                    | "error_message_for_obj_recursive"
                    | "validate!"
            );
        }
        false
    }

    pub(super) fn static_type_description(&self, node: &Node<'_>) -> String {
        if let Some(call) = node.as_call_node() {
            if prism::constant_name(call.name()) == "first" {
                if let Some(receiver) = call.receiver() {
                    if receiver.as_array_node().is_some() {
                        if let Some(array) = receiver.as_array_node() {
                            if let Some(element) = array.elements().first() {
                                return prism::text(self.source, &element);
                            }
                        }
                    }
                }
            }
        }
        let source = prism::text(self.source, node);
        if source.contains("T.self_type") {
            "T.untyped".to_owned()
        } else {
            source
        }
    }

    pub(super) fn eval_call<'node, C: CallShape<'node>>(
        &mut self,
        node: &Node<'node>,
        call: &C,
        environment: &mut Environment,
    ) -> Eval {
        let name = call.name();
        let argument_inputs = call.argument_inputs();
        let evaluated = self.evaluate_call_arguments(argument_inputs, environment);
        let arguments = evaluated.arguments;
        let argument_types = &arguments.argument_types;
        let mut abrupt = evaluated.abrupt;
        let mut abrupt_flow = evaluated.abrupt_flow;
        let mut all_normal = evaluated.all_normal;
        let receiver_node = call.receiver();
        let block = call.block();
        self.observe_define_method_binding(&name, &arguments, block.as_ref(), environment);
        let preserve_nested_literal_tuples = receiver_node.as_ref().is_some_and(|receiver| {
            receiver.as_array_node().is_some()
                && block
                    .as_ref()
                    .is_some_and(Self::block_has_multiple_required_parameters)
        });
        let mut receiver_type = if let Some(receiver) = receiver_node.as_ref() {
            let previous_preserve_nested_literal_tuples = self.preserve_nested_literal_tuples;
            self.preserve_nested_literal_tuples |= preserve_nested_literal_tuples;
            let result = self.eval_node(receiver, environment);
            self.preserve_nested_literal_tuples = previous_preserve_nested_literal_tuples;
            abrupt = abrupt.join(&result.abrupt);
            abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
            all_normal &= result.flow.contains(FlowKind::Normal);
            result.type_
        } else {
            Type::Object
        };
        // A block argument is an ordinary Ruby expression.  Evaluate it even
        // when the callee is dynamic and therefore has no block signature to
        // consume it; otherwise expressions such as `klass.new(&block)` leave
        // the `block` send unrecorded and hide its type from the caller.
        if let Some(expression) = block
            .as_ref()
            .and_then(|block| block.as_block_argument_node())
            .and_then(|block| block.expression())
        {
            let result = self.eval_node(&expression, environment);
            abrupt = abrupt.join(&result.abrupt);
            abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
            all_normal &= result.flow.contains(FlowKind::Normal);
        }
        let array_write_receiver_type = receiver_type.clone();
        let dynamic_eval_receiver = if receiver_node.is_none() {
            environment.self_type.clone()
        } else {
            receiver_type.clone()
        };
        if matches!(name.as_str(), "push" | "<<" | "prepend") {
            if let Some(local) = receiver_node
                .as_ref()
                .and_then(Node::as_local_variable_read_node)
            {
                let local_name = prism::constant_name(local.name());
                if environment.open_array_locals.contains(&local_name) {
                    if let Type::Array(element) = &receiver_type {
                        let widened = argument_types
                            .iter()
                            .fold(element.as_ref().clone(), |current, actual| {
                                current.join(actual)
                            });
                        receiver_type = Type::Array(Box::new(widened));
                    }
                }
            }
        }
        let static_type_receiver = receiver_node
            .as_ref()
            .is_some_and(|receiver| self.static_type_value(receiver));
        if static_type_receiver
            && !matches!(
                name.as_str(),
                "new"
                    | "valid?"
                    | "recursively_valid?"
                    | "subtype_of?"
                    | "describe_obj"
                    | "error_message_for_obj"
                    | "error_message_for_obj_recursive"
                    | "validate!"
                    | "params"
                    | "returns"
                    | "void"
                    | "bind"
            )
        {
            if let Some(receiver) = receiver_node.as_ref() {
                let description = match receiver_type {
                    Type::AttachedClassOf(ref owner) => {
                        format!("T.attached_class (of {owner})")
                    }
                    _ => self.static_type_description(receiver),
                };
                self.error(
                    node,
                    format!(
                        "Call to method `{name}` on `{description}` mistakes a type for a value"
                    ),
                );
            }
        }
        if call.is_safe_navigation()
            && !receiver_type.is_any()
            && !receiver_type.contains_any()
            && !receiver_type.is_never()
            && !matches!(receiver_type, Type::Anything)
            && receiver_type.without(&Type::Nil) == receiver_type
        {
            self.error(
                node,
                format!("Used `&.` operator on `{receiver_type}`, which can never be nil"),
            );
        }
        // Sorbet's `T.proc` expressions are runtime type objects when they
        // appear outside a signature declaration (for example as the second
        // argument to `T.cast`).  Preserve the parsed proc shape instead of
        // treating the chained `.params/.returns/.void` calls as an unknown
        // application method.  The signature parser already understands the
        // complete expression, including nested `T.nilable` and `bind`.
        let runtime_proc_type_expression =
            self.static_type_value(node) && prism::text(self.source, node).contains("T.proc");
        let mut untyped_origin = None;
        let mut callee_type = if let Some(type_) = self.eval_dynamic_instance_variable_call(
            &name,
            receiver_node.as_ref(),
            &receiver_type,
            &arguments.argument_nodes,
            argument_types,
            environment,
        ) {
            type_
        } else if runtime_proc_type_expression {
            self.runtime_type_object_type(node)
        } else if receiver_node.as_ref().is_some_and(|receiver| {
            self.constant_reference_name(receiver)
                .is_some_and(|name| name.trim_start_matches("::") == "T")
        }) {
            let type_ = self.eval_t_call(
                node,
                &name,
                &arguments.argument_nodes,
                argument_types,
                environment,
            );
            if type_.contains_any() {
                untyped_origin = Some(if name == "unsafe" {
                    UntypedOrigin::Unsafe
                } else if arguments
                    .argument_nodes
                    .iter()
                    .any(|argument| prism::text(self.source, argument).contains("T.untyped"))
                {
                    UntypedOrigin::ExplicitAnnotation
                } else {
                    UntypedOrigin::FallbackCall
                });
            }
            type_
        } else if let Some(type_) =
            self.eval_dynamic_eval_call(&name, &dynamic_eval_receiver, block.as_ref(), environment)
        {
            type_
        } else if name == "application"
            && receiver_node.as_ref().is_some_and(|receiver| {
                self.constant_reference_name(receiver)
                    .is_some_and(|constant| constant.trim_start_matches("::") == "Rails")
            })
        {
            self.rails_application_instance_type().unwrap_or(Type::Any)
        } else if name == "routes" && self.is_rails_application_instance(&receiver_type) {
            Type::named("ActionDispatch::Routing::RouteSet")
        } else if receiver_node.is_none()
            && matches!(name.as_str(), "lambda" | "proc")
            && call.block().is_some()
        {
            let (parameters, return_type) = call.block().as_ref().map_or_else(
                || (Vec::new(), Type::Any),
                |block| {
                    if block.as_block_argument_node().is_some() {
                        let type_ = self
                            .passed_block_expression_type(block, environment)
                            .and_then(|type_| Self::passed_block_signature(&type_))
                            .unwrap_or_else(|| Type::Proc(Vec::new(), Box::new(Type::Any)));
                        if let Type::Proc(parameters, return_type) = type_ {
                            return (parameters, *return_type);
                        }
                        return (Vec::new(), Type::Any);
                    }
                    let signature = Self::inferred_block_signature(block);
                    let return_type = self.eval_block_node(block, &signature.params, environment);
                    (signature.params, return_type)
                },
            );
            Type::Proc(parameters, Box::new(return_type))
        } else if receiver_node.is_none()
            && matches!(
                &environment.self_type,
                Type::Union(_) | Type::Intersection(_)
            )
            && self
                .resolve_method_key(&self.implicit_method_key(&name, environment))
                .is_none()
        {
            // A predicate can refine implicit `self` to a union.  Dispatch
            // calls made without an explicit receiver through each member,
            // just like `value.children` on a union, instead of trying to
            // synthesize one method key for the whole union.
            let receiver_type = environment.self_type.clone();
            let global_type = self.eval_global_call(
                node,
                &name,
                &arguments.argument_nodes,
                argument_types,
                block.as_ref(),
                environment,
            );
            if !global_type.is_any() {
                global_type
            } else {
                let site = CallSite {
                    argument_nodes: &arguments.argument_nodes,
                    argument_types,
                    block: block.as_ref(),
                };
                let (type_, fallback_origin) = self.eval_polymorphic_receiver_call(
                    node,
                    None,
                    &receiver_type,
                    &name,
                    &arguments,
                    block.as_ref(),
                    &site,
                    environment,
                );
                if type_.contains_any() {
                    untyped_origin = Some(fallback_origin);
                }
                if type_.is_any() {
                    self.report_missing_method_if_needed(node, &receiver_type, &name, false);
                }
                type_
            }
        } else if receiver_node.is_none() {
            if name == "extend" {
                self.observe_extend_hook(node, &arguments.argument_nodes, environment);
            } else if name == "include" {
                self.observe_include_hook(node, &arguments.argument_nodes, environment);
            }
            if name == "each"
                && Self::named_type_name(&environment.self_type)
                    .is_some_and(|owner| name_matches(&owner, "Enumerable"))
            {
                if let Some(block) = block.as_ref() {
                    let _ = self.eval_block_node(block, &[Type::Any], environment);
                }
            }
            let key = self.implicit_method_key(&name, environment);
            let receiver_type = environment.self_type.clone();
            let method_resolved = self.resolve_method_key(&key).is_some();
            let random_formatter_signature =
                self.random_formatter_signature(None, &receiver_type, &name);
            let resolved_owner = self
                .resolve_method_key(&key)
                .and_then(|resolved| resolved.owner);
            let tsort_type = self.eval_tsort_method(
                &receiver_type,
                &name,
                environment,
                resolved_owner.as_deref(),
            );
            self.record_method_dependency(&key, environment);
            if name == "Array" {
                // Ruby's Kernel#Array is a coercion operation, not a normal
                // generic identity function. Its Sorbet RBI signature is
                // necessarily broad enough to describe Enumerable inputs,
                // but using that signature directly infers `Array[String |
                // Array[String]]` for a union input. The runtime result is an
                // array of the input's elements, so use the structural model
                // here before generic signature inference.
                self.eval_global_call(
                    node,
                    &name,
                    &arguments.argument_nodes,
                    argument_types,
                    block.as_ref(),
                    environment,
                )
            } else if let Some(signature) = random_formatter_signature {
                self.invoke_signature(
                    node,
                    &name,
                    &signature,
                    &arguments,
                    Some(&receiver_type),
                    None,
                )
            } else if let Some(type_) = tsort_type {
                type_
            } else if let Some((accessor_key, accessor)) = self
                .resolve_method_key(&key)
                .filter(|resolved| {
                    self.declarations
                        .methods
                        .get(resolved)
                        .is_some_and(|state| !state.explicit)
                })
                .and_then(|resolved| {
                    self.declarations
                        .accessors
                        .get(&resolved)
                        .copied()
                        .map(|accessor| (resolved, accessor))
                })
            {
                let type_ =
                    self.eval_accessor_call(&accessor_key, accessor, argument_types, environment);
                if type_.contains_any() {
                    untyped_origin = Some(UntypedOrigin::InferredMethod);
                }
                type_
            } else if name == "autoload"
                && Self::class_object_instance_type(&receiver_type).is_some()
            {
                // Module#autoload (including ActiveSupport's forwarding
                // override) registers a loader and returns nil.  Prefer this
                // concrete Ruby contract over an untyped external declaration.
                Type::Nil
            } else if matches!(name.as_str(), "__method__" | "__callee__")
                && environment
                    .method_key
                    .as_ref()
                    .is_some_and(|key| !key.name.starts_with('<'))
            {
                // The core RBI must be nilable because these keywords are
                // also valid at top level. Inside a real method Ruby always
                // supplies its name as a Symbol.
                Type::Symbol
            } else if name == "private_class_method"
                && arguments
                    .argument_nodes
                    .iter()
                    .any(|argument| argument.as_def_node().is_some())
            {
                // `private_class_method def self.foo ... end` is Ruby's
                // declaration form.  The core RBI also exposes
                // `private_class_method` as a callable taking method names,
                // but applying that signature to a DefNode makes the
                // declaration itself look like an invalid runtime argument.
                // MethodRegistrar has already recorded the definition and
                // visibility override, so the declaration evaluates to nil.
                Type::Nil
            } else if let Some(signature) = self
                .observe_call(&key, &arguments, block.is_some())
                .map(|signature| self.widen_overridable_noreturn(&key, signature))
            {
                let declared = self
                    .resolve_method_key(&key)
                    .and_then(|resolved| self.declarations.methods.get(&resolved))
                    .is_some_and(|state| state.explicit);
                let block_return_type = self.observe_block_call(
                    &key,
                    block.as_ref(),
                    &signature,
                    &arguments,
                    Some(&receiver_type),
                    environment,
                );
                let type_ = self.invoke_signature(
                    node,
                    &name,
                    &signature,
                    &arguments,
                    Some(&environment.self_type),
                    block_return_type.as_ref(),
                );
                let type_ = self.widen_recursive_call_return(&key, type_, environment);
                if type_.contains_any() {
                    untyped_origin = Some(if declared {
                        UntypedOrigin::DeclaredSignature
                    } else {
                        UntypedOrigin::InferredMethod
                    });
                }
                type_
            } else if key.singleton {
                if let Some(owner) = key.owner.clone() {
                    if name == "new" {
                        self.infer_initializer_call(
                            node,
                            &owner,
                            &arguments,
                            block.is_some(),
                            environment,
                        );
                        if environment.method_key.as_ref().is_some_and(|method| {
                            method.singleton
                                && !matches!(
                                    method.name.as_str(),
                                    "<bound-block>"
                                        | "<class-body>"
                                        | "<module-body>"
                                        | "<singleton-body>"
                                )
                        }) {
                            Type::AttachedClassOf(owner)
                        } else {
                            Type::named(owner)
                        }
                    } else {
                        let type_ = self.eval_global_call(
                            node,
                            &name,
                            &arguments.argument_nodes,
                            argument_types,
                            block.as_ref(),
                            environment,
                        );
                        if type_.contains_any() {
                            untyped_origin = Some(UntypedOrigin::FallbackCall);
                        }
                        if type_.is_any()
                            && !environment
                                .method_key
                                .as_ref()
                                .is_some_and(|method| method.name == "<bound-block>")
                        {
                            self.report_missing_method_if_needed(
                                node,
                                &receiver_type,
                                &name,
                                method_resolved,
                            );
                        }
                        if type_.is_any()
                            && environment
                                .method_key
                                .as_ref()
                                .is_some_and(|method| method.name == "<bound-block>")
                        {
                            self.error(
                                node,
                                format!(
                                    "Method `{name}` does not exist on `{}`",
                                    Self::sorbet_type_description(&environment.self_type)
                                ),
                            );
                        }
                        type_
                    }
                } else {
                    let type_ = self.eval_global_call(
                        node,
                        &name,
                        &arguments.argument_nodes,
                        argument_types,
                        block.as_ref(),
                        environment,
                    );
                    if type_.contains_any() {
                        untyped_origin = Some(UntypedOrigin::FallbackCall);
                    }
                    if type_.is_any()
                        && !environment
                            .method_key
                            .as_ref()
                            .is_some_and(|method| method.name == "<bound-block>")
                    {
                        self.report_missing_method_if_needed(
                            node,
                            &receiver_type,
                            &name,
                            method_resolved,
                        );
                    }
                    type_
                }
            } else {
                if name == "new"
                    && environment
                        .method_key
                        .as_ref()
                        .is_some_and(|method| method.name == "<bound-block>")
                {
                    self.error(node, "Method `new` does not exist");
                    Type::Any
                } else {
                    let type_ = self.eval_global_call(
                        node,
                        &name,
                        &arguments.argument_nodes,
                        argument_types,
                        block.as_ref(),
                        environment,
                    );
                    if type_.contains_any() {
                        untyped_origin = Some(UntypedOrigin::FallbackCall);
                    }
                    if type_.is_any()
                        && environment
                            .method_key
                            .as_ref()
                            .is_some_and(|method| method.name == "<bound-block>")
                    {
                        self.error(
                            node,
                            format!(
                                "Method `{name}` does not exist on `{}`",
                                Self::sorbet_type_description(&environment.self_type)
                            ),
                        );
                    }
                    if type_.is_any()
                        && !environment
                            .method_key
                            .as_ref()
                            .is_some_and(|method| method.name == "<bound-block>")
                    {
                        self.report_missing_method_if_needed(
                            node,
                            &receiver_type,
                            &name,
                            method_resolved,
                        );
                    }
                    type_
                }
            }
        } else {
            let site = CallSite {
                argument_nodes: &arguments.argument_nodes,
                argument_types,
                block: block.as_ref(),
            };
            let nonempty_literal_extremum = matches!(name.as_str(), "min" | "max")
                && argument_types.is_empty()
                && receiver_node.as_ref().is_some_and(|receiver| {
                    receiver
                        .as_array_node()
                        .is_some_and(|array| !array.elements().is_empty())
                });
            let nonempty_array_access = matches!(name.as_str(), "first" | "last")
                && argument_types.is_empty()
                && receiver_node
                    .as_ref()
                    .and_then(Node::as_local_variable_read_node)
                    .is_some_and(|local| {
                        environment.known_nonempty_array(&prism::constant_name(local.name()))
                    });
            let open_array_append = matches!(name.as_str(), "push" | "<<" | "prepend")
                && receiver_node.as_ref().is_some_and(|receiver| {
                    self.is_open_array_append_receiver(receiver, environment)
                });
            let dispatch_receiver_type = if call.is_safe_navigation() {
                receiver_type.without(&Type::Nil)
            } else if open_array_append && matches!(receiver_type, Type::Array(_) | Type::Tuple(_))
            {
                // An append expression rooted in an open array can be chained
                // (`values << :symbol << integer`).  The nested expression's
                // ordinary result is precise, but the open root still permits
                // the outer append to widen the array element type.
                Type::Array(Box::new(Type::Any))
            } else {
                receiver_type.clone()
            };
            let struct_constructor = name == "new"
                && receiver_node.as_ref().is_some_and(|receiver| {
                    self.constant_reference_name(receiver)
                        .is_some_and(|name| name.trim_start_matches("::") == "Struct")
                });
            let yaml_dump = name == "dump"
                && argument_types.len() == 1
                && receiver_node.as_ref().is_some_and(|receiver| {
                    self.constant_reference_name(receiver)
                        .is_some_and(|name| name.trim_start_matches("::") == "YAML")
                });
            let class_mixin = matches!(name.as_str(), "include" | "prepend" | "extend")
                && Self::class_object_instance_types(&dispatch_receiver_type).is_some();
            let random_formatter_signature = self.random_formatter_signature(
                receiver_node.as_ref(),
                &dispatch_receiver_type,
                &name,
            );
            let mut result = if class_mixin {
                if name == "include" {
                    self.observe_include_hook_for_base(
                        node,
                        &arguments.argument_nodes,
                        &dispatch_receiver_type,
                        environment,
                    );
                } else if name == "extend" {
                    self.observe_extend_hook_for_base(
                        node,
                        &arguments.argument_nodes,
                        &dispatch_receiver_type,
                        environment,
                    );
                }
                Type::Nil
            } else if yaml_dump {
                Type::String
            } else if struct_constructor {
                Self::class_object_type("Struct")
            } else if let Some(signature) = random_formatter_signature {
                self.invoke_signature(
                    node,
                    &name,
                    &signature,
                    &arguments,
                    Some(&dispatch_receiver_type),
                    None,
                )
            } else if matches!(
                dispatch_receiver_type,
                Type::Union(_) | Type::Intersection(_)
            ) || matches!(
                &dispatch_receiver_type,
                Type::Named(name, arguments)
                    if (name_matches(name, "Class") || name_matches(name, "Module"))
                        && arguments
                            .first()
                            .is_some_and(|argument| matches!(argument, Type::Intersection(_)))
            ) {
                let (type_, fallback_origin) = self.eval_polymorphic_receiver_call(
                    node,
                    receiver_node.as_ref(),
                    &dispatch_receiver_type,
                    &name,
                    &arguments,
                    block.as_ref(),
                    &site,
                    environment,
                );
                if type_.contains_any() {
                    untyped_origin = Some(fallback_origin);
                }
                type_
            } else if let Some(key) = self.receiver_method_key(
                receiver_node.as_ref(),
                &dispatch_receiver_type,
                &name,
                environment,
            ) {
                let method_resolved = self.resolve_method_key(&key).is_some();
                let resolved_owner = self
                    .resolve_method_key(&key)
                    .and_then(|resolved| resolved.owner);
                let tsort_type = self.eval_tsort_method(
                    &dispatch_receiver_type,
                    &name,
                    environment,
                    resolved_owner.as_deref(),
                );
                self.record_method_dependency(&key, environment);
                if self
                    .resolve_method_key(&key)
                    .and_then(|resolved| self.declarations.methods.get(&resolved))
                    .is_some_and(|state| state.visibility == Visibility::Private)
                    && !self.private_call_allowed(&key, environment)
                {
                    self.error(
                        node,
                        format!(
                            "Non-private call to private method `{name}` on `{dispatch_receiver_type}`"
                        ),
                    );
                }
                if open_array_append {
                    self.eval_method_call(&dispatch_receiver_type, &name, &site, environment)
                } else if let Some(type_) = tsort_type {
                    type_
                } else if matches!(&dispatch_receiver_type, Type::Tuple(_))
                    && matches!(name.as_str(), "first" | "last")
                    && argument_types.is_empty()
                {
                    // A fixed tuple is more precise than the generic Array
                    // RBI: preserve its positional component for methods
                    // such as `first` and `last`.
                    self.eval_method_call(&dispatch_receiver_type, &name, &site, environment)
                } else if matches!(&dispatch_receiver_type, Type::Tuple(_))
                    && name == "[]"
                    && matches!(argument_types.first(), Some(Type::Integer))
                {
                    // An explicit generic Array#[] RBI must not erase the
                    // positional information carried by a fixed tuple.
                    // Dispatch the structural operation so an integer index
                    // retains the union of the tuple's actual components.
                    self.eval_method_call(&dispatch_receiver_type, &name, &site, environment)
                } else if matches!(&dispatch_receiver_type, Type::Array(_) | Type::Tuple(_))
                    && self
                        .resolve_method_key(&key)
                        .and_then(|resolved| self.declarations.methods.get(&resolved))
                        .is_some_and(|state| !state.explicit)
                {
                    // The core Array RBI declares many methods without a
                    // return contract. Prefer the structural Array model for
                    // those methods instead of interpreting the absent body
                    // as `T.noreturn`.
                    let type_ =
                        self.eval_method_call(&dispatch_receiver_type, &name, &site, environment);
                    if type_.contains_any() {
                        untyped_origin = Some(UntypedOrigin::FallbackCall);
                    }
                    type_
                } else if (name == "new"
                    && Self::class_object_instance_type(&dispatch_receiver_type)
                        .and_then(|instance| Self::named_type_name(&instance))
                        .is_some_and(|class| name_matches(&class, "OptionParser")))
                    || (matches!(name.as_str(), "on" | "parse!")
                        && matches!(
                            &dispatch_receiver_type,
                            Type::Named(class, _) if name_matches(class, "OptionParser")
                        ))
                {
                    let type_ =
                        self.eval_method_call(&dispatch_receiver_type, &name, &site, environment);
                    if type_.contains_any() {
                        untyped_origin = Some(UntypedOrigin::FallbackCall);
                    }
                    type_
                } else {
                    let inferred_accessor = self
                        .resolve_method_key(&key)
                        .filter(|resolved| {
                            self.declarations
                                .methods
                                .get(resolved)
                                .is_some_and(|state| !state.explicit)
                        })
                        .and_then(|resolved| {
                            self.declarations
                                .accessors
                                .get(&resolved)
                                .copied()
                                .map(|accessor| (resolved, accessor))
                        });
                    if let Some((accessor_key, accessor)) = inferred_accessor {
                        let type_ = self.eval_accessor_call(
                            &accessor_key,
                            accessor,
                            argument_types,
                            environment,
                        );
                        if type_.contains_any() {
                            untyped_origin = Some(UntypedOrigin::InferredMethod);
                        }
                        type_
                    } else if let Some(signature) = self
                        .observe_call(&key, &arguments, block.is_some())
                        .map(|signature| self.widen_overridable_noreturn(&key, signature))
                    {
                        let declared = self
                            .resolve_method_key(&key)
                            .and_then(|resolved| self.declarations.methods.get(&resolved))
                            .is_some_and(|state| state.explicit);
                        let block_return_type = self.observe_block_call(
                            &key,
                            block.as_ref(),
                            &signature,
                            &arguments,
                            Some(&dispatch_receiver_type),
                            environment,
                        );
                        let type_ = if let Some(type_) = self.eval_node_helpers_method(
                            &dispatch_receiver_type,
                            &name,
                            argument_types,
                        ) {
                            type_
                        } else {
                            self.invoke_signature(
                                node,
                                &name,
                                &signature,
                                &arguments,
                                Some(&dispatch_receiver_type),
                                block_return_type.as_ref(),
                            )
                        };
                        let type_ = self.widen_recursive_call_return(&key, type_, environment);
                        let type_ = if name == "new"
                            && Self::class_object_instance_type(&dispatch_receiver_type).is_some()
                        {
                            self.instantiate_generic_class(type_)
                        } else {
                            type_
                        };
                        if type_.contains_any() {
                            untyped_origin = Some(if declared {
                                UntypedOrigin::DeclaredSignature
                            } else {
                                UntypedOrigin::InferredMethod
                            });
                        }
                        type_
                    } else {
                        let type_ = self.eval_method_call(
                            &dispatch_receiver_type,
                            &name,
                            &site,
                            environment,
                        );
                        if type_.contains_any() {
                            untyped_origin = Some(if dispatch_receiver_type.contains_any() {
                                UntypedOrigin::Propagated
                            } else {
                                UntypedOrigin::FallbackCall
                            });
                        }
                        if type_.is_any() {
                            self.report_missing_method_if_needed(
                                node,
                                &dispatch_receiver_type,
                                &name,
                                method_resolved,
                            );
                        }
                        type_
                    }
                }
            } else {
                let type_ = if dispatch_receiver_type == Type::Anything {
                    self.error(
                        node,
                        format!("Method `{name}` does not exist on `T.anything`"),
                    );
                    Type::Any
                } else {
                    self.eval_method_call(&dispatch_receiver_type, &name, &site, environment)
                };
                if type_.contains_any() {
                    untyped_origin = Some(if dispatch_receiver_type.contains_any() {
                        UntypedOrigin::Propagated
                    } else {
                        UntypedOrigin::FallbackCall
                    });
                }
                if type_.is_any() {
                    self.report_missing_method_if_needed(
                        node,
                        &dispatch_receiver_type,
                        &name,
                        false,
                    );
                }
                type_
            };
            if nonempty_literal_extremum || nonempty_array_access {
                result = result.without(&Type::Nil);
            }
            self.refine_local_array_write(
                receiver_node.as_ref(),
                &name,
                argument_types,
                &array_write_receiver_type,
                environment,
            );
            self.refine_local_hash_write(
                receiver_node.as_ref(),
                &name,
                argument_types,
                &dispatch_receiver_type,
                environment,
            );
            if !struct_constructor
                && name == "new"
                && receiver_node.as_ref().is_some_and(|receiver| {
                    receiver.as_self_node().is_some()
                        || self.constant_reference_name(receiver).is_some()
                        || receiver.as_local_variable_read_node().is_some()
                })
            {
                let owners = Self::class_object_instance_types(&receiver_type)
                    .unwrap_or_default()
                    .into_iter()
                    .filter_map(|instance| Self::named_type_name(&instance))
                    .collect::<Vec<_>>();
                let owners = if owners.is_empty()
                    && !matches!(
                        &receiver_type,
                        Type::Named(name, _) if name_matches(name, "Class") || name_matches(name, "Module")
                    ) {
                    Self::named_type_name(&receiver_type)
                        .into_iter()
                        .collect::<Vec<_>>()
                } else {
                    owners
                };
                let mut constructed = Type::Never;
                for owner in owners {
                    let candidate_receiver = Self::class_object_type(&owner);
                    let has_explicit_new = self
                        .receiver_method_key(
                            receiver_node.as_ref(),
                            &candidate_receiver,
                            &name,
                            environment,
                        )
                        .and_then(|key| self.resolve_method_key(&key))
                        .is_some_and(|resolved| {
                            // `Class#new` is the generic Ruby constructor and
                            // must not prevent us from observing the target
                            // class's `initialize` method. Only a `new`
                            // declared on the class itself is an override.
                            resolved.owner.as_deref() == Some(owner.as_str())
                        });
                    if has_explicit_new {
                        continue;
                    }
                    self.infer_initializer_call(
                        node,
                        &owner,
                        &arguments,
                        block.is_some(),
                        environment,
                    );
                    self.observe_struct_constructor(&owner, &arguments);
                    constructed = constructed.join(&if self
                        .substitution_context
                        .as_ref()
                        .filter(|context| context.singleton)
                        .and_then(|context| context.owner.as_deref())
                        .is_some_and(|context_owner| context_owner == owner)
                    {
                        Type::AttachedClassOf(owner)
                    } else {
                        self.instantiate_generic_class(Type::named(owner))
                    });
                }
                if !constructed.is_never() {
                    result = constructed;
                }
            }
            if call.is_safe_navigation() && !receiver_type.is_any() {
                Type::union([Type::Nil, result])
            } else {
                result
            }
        };

        if name == "!" {
            // Even when a builtin RBI specializes TrueClass#! or FalseClass#!,
            // Ruby's unary negation is exposed as the boolean protocol.
            callee_type = Type::bool();
        }

        // Ruby setter calls evaluate to the assigned value, regardless of the
        // setter method's declared return type. Equality and ordering methods
        // end in `=` too, but are ordinary predicates/comparators.
        if name.ends_with('=')
            && !matches!(name.as_str(), "==" | "!=" | "<=" | ">=" | "===")
            && (arguments.argument_types.len() == 1 || name == "[]=")
        {
            if let Some(type_) = arguments.argument_types.last() {
                callee_type = type_.clone();
            }
        }

        if callee_type.contains_any() {
            let (start, end) = prism::span(node);
            self.untyped_origins.insert(
                (start, end),
                untyped_origin.unwrap_or(UntypedOrigin::Propagated),
            );
        }

        let terminates =
            all_normal && self.call_terminates(call, environment, &receiver_type, &callee_type);
        let (normal_type, callee_abrupt, callee_flow) = if all_normal {
            if terminates {
                (
                    None,
                    OutcomeTypes::for_kind(FlowKind::Raise, callee_type),
                    Flow::abrupt(FlowKind::Raise),
                )
            } else {
                (Some(callee_type), OutcomeTypes::default(), Flow::normal())
            }
        } else {
            (None, OutcomeTypes::default(), Flow::empty())
        };
        Eval::from_parts(
            normal_type,
            abrupt.join(&callee_abrupt),
            abrupt_flow.union(callee_flow),
        )
    }
}
