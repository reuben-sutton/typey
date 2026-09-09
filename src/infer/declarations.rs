use super::{MethodKey, MethodState, ParameterShape};
use crate::diagnostic::Diagnostic;
use crate::prism;
use crate::signature::{self, AssertionKind, MethodSig};
use crate::types::Type;
use ruby_prism::{CallNode, ClassNode, DefNode, Node, Visit};
use std::collections::BTreeSet;
use std::collections::{BTreeMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AccessorKind {
    Reader,
    Writer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Visibility {
    Public,
    Private,
    Protected,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct GenericMember {
    pub(super) index: usize,
    pub(super) fixed: Option<Type>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct ClassInfo {
    pub(super) is_module: bool,
    pub(super) extend_self: bool,
    pub(super) attached_class_member: Option<usize>,
    pub(super) superclass: Option<String>,
    pub(super) struct_fields: Option<Vec<String>>,
    pub(super) includes: Vec<String>,
    pub(super) prepends: Vec<String>,
    pub(super) extends: Vec<String>,
    pub(super) class_methods: Vec<String>,
    pub(super) requires_ancestors: Vec<String>,
    pub(super) type_members: BTreeMap<String, GenericMember>,
}

pub(super) fn attribute_writer_signature(signature: &MethodSig) -> MethodSig {
    if !signature.params.is_empty()
        || !signature.keywords.is_empty()
        || signature.accepts_rest
        || signature.block.is_some()
    {
        return signature.clone();
    }

    let mut writer = signature.clone();
    writer.params = vec![signature.return_type.clone()];
    writer.required_params = 1;
    writer
}

/// Source and RBI declarations owned by the analyzer.
///
/// Keeping declaration storage together is important because method lookup,
/// generated accessors, aliases, constants, and nominal-name indexes are one
/// evolving graph. The evaluator may query this graph, but it should not need
/// to know which maps implement it.
#[derive(Default)]
pub(super) struct DeclarationState {
    pub(super) methods: BTreeMap<MethodKey, MethodState>,
    pub(super) definitions: BTreeMap<usize, MethodKey>,
    pub(super) parameter_shapes: BTreeMap<usize, ParameterShape>,
    pub(super) classes: BTreeMap<String, ClassInfo>,
    pub(super) class_name_set: HashSet<String>,
    pub(super) class_name_suffixes: BTreeMap<String, Vec<String>>,
    pub(super) aliases: BTreeMap<MethodKey, MethodKey>,
    pub(super) accessors: BTreeMap<MethodKey, AccessorKind>,
    pub(super) type_aliases: BTreeMap<String, Type>,
    pub(super) constants: BTreeMap<String, Type>,
    pub(super) constant_name_set: HashSet<String>,
    pub(super) constant_name_suffixes: BTreeMap<String, Vec<String>>,
    pub(super) struct_fields: BTreeMap<String, Vec<String>>,
    pub(super) struct_field_types: BTreeMap<(String, String), Type>,
}
pub(super) struct MethodRegistrar<'a> {
    source: &'a [u8],
    diagnostics: &'a mut Vec<Diagnostic>,
    declarations: &'a mut DeclarationState,
    attribute_annotations: &'a BTreeMap<usize, Vec<MethodSig>>,
    class_type_parameters: &'a BTreeMap<usize, Vec<String>>,
    assertions: &'a BTreeMap<usize, signature::InlineAssertion>,
    class_stack: Vec<String>,
    singleton_stack: Vec<String>,
    dynamic_definition_stack: Vec<(String, bool)>,
    visibility_stack: Vec<Visibility>,
    visibility_overrides: BTreeMap<MethodKey, Visibility>,
    method_depth: usize,
}

impl<'a> MethodRegistrar<'a> {
    pub(super) fn new(
        source: &'a [u8],
        diagnostics: &'a mut Vec<Diagnostic>,
        declarations: &'a mut DeclarationState,
        attribute_annotations: &'a BTreeMap<usize, Vec<MethodSig>>,
        class_type_parameters: &'a BTreeMap<usize, Vec<String>>,
        assertions: &'a BTreeMap<usize, signature::InlineAssertion>,
    ) -> Self {
        Self {
            source,
            diagnostics,
            declarations,
            attribute_annotations,
            class_type_parameters,
            assertions,
            class_stack: Vec::new(),
            singleton_stack: Vec::new(),
            dynamic_definition_stack: Vec::new(),
            visibility_stack: Vec::new(),
            visibility_overrides: BTreeMap::new(),
            method_depth: 0,
        }
    }
}

fn trim_ascii_whitespace(bytes: &[u8]) -> &[u8] {
    let start = bytes
        .iter()
        .position(|byte| !byte.is_ascii_whitespace())
        .unwrap_or(bytes.len());
    let end = bytes
        .iter()
        .rposition(|byte| !byte.is_ascii_whitespace())
        .map_or(start, |offset| offset + 1);
    &bytes[start..end]
}

impl MethodRegistrar<'_> {
    fn inline_constant_type<'node>(&self, node: &Node<'node>) -> Option<Type> {
        let (_, end) = prism::span(node);
        let line = self.source[..end]
            .iter()
            .filter(|byte| **byte == b'\n')
            .count();
        let assertion = self.assertions.get(&line)?;
        if assertion.kind != AssertionKind::Let || assertion.offset < end {
            return None;
        }
        if self.source[end..assertion.offset]
            .iter()
            .any(|byte| !byte.is_ascii_whitespace() && *byte != b',')
        {
            return None;
        }
        Some(assertion.type_.clone())
    }

    fn for_each_preceding_comment_line(
        &self,
        node: &Node<'_>,
        mut visit: impl FnMut(&[u8]) -> bool,
    ) {
        let mut end = prism::span(node).0;
        loop {
            while end > 0 && matches!(self.source[end - 1], b'\n' | b'\r') {
                end -= 1;
            }
            let line_start = self.source[..end]
                .iter()
                .rposition(|byte| *byte == b'\n')
                .map_or(0, |offset| offset + 1);
            let line = trim_ascii_whitespace(&self.source[line_start..end]);
            if line.is_empty() {
                // Keep looking past blank lines, matching `str::lines().rev()`.
            } else if line.first() != Some(&b'#') || !visit(line) {
                break;
            }

            if line_start == 0 {
                break;
            }
            end = line_start - 1;
        }
    }

    fn has_preceding_annotation(&self, node: &Node<'_>, annotation: &str) -> bool {
        let annotation = annotation.as_bytes();
        let mut found = false;
        self.for_each_preceding_comment_line(node, |line| {
            found = annotation.is_empty()
                || line
                    .windows(annotation.len())
                    .any(|window| window == annotation);
            !found
        });
        found
    }

    fn report_interface_on_class(&mut self, node: &Node<'_>) {
        if self.has_preceding_annotation(node, "@interface") {
            let (start, end) = prism::span(node);
            self.diagnostics.push(Diagnostic::error(
                self.source,
                "Classes can't be interfaces. Use `abstract!` instead of `interface!`",
                start,
                end,
            ));
        }
    }

    fn class_extends_t_struct(&self, owner: &str) -> bool {
        let mut current = Some(owner.to_owned());
        let mut visited = BTreeSet::new();
        while let Some(name) = current {
            if !visited.insert(name.clone()) {
                return false;
            }
            if name.trim_start_matches("::") == "T::Struct" {
                return true;
            }
            current = self
                .declarations
                .classes
                .get(&name)
                .and_then(|info| info.superclass.clone());
        }
        false
    }

    fn register_struct_property<'node>(&mut self, node: &CallNode<'node>, immutable: bool) {
        if self.method_depth != 0 {
            return;
        }
        let Some(owner) = self
            .singleton_stack
            .last()
            .or_else(|| self.class_stack.last())
            .cloned()
        else {
            return;
        };
        if !self.class_extends_t_struct(&owner) {
            return;
        }
        let Some(arguments) = node.arguments() else {
            return;
        };
        let Some(name_node) = arguments.arguments().into_iter().next() else {
            return;
        };
        let field = self.method_name(&name_node);
        if field.is_empty() {
            return;
        }
        let Some(type_node) = arguments.arguments().into_iter().nth(1) else {
            return;
        };
        let type_ = signature::parse_type(&prism::text(self.source, &type_node));
        let reader = MethodKey {
            owner: Some(owner.clone()),
            name: field.clone(),
            singleton: false,
        };
        let reader_signature = MethodSig::new(Vec::new(), type_);
        self.declarations
            .accessors
            .insert(reader.clone(), AccessorKind::Reader);
        self.declarations.methods.entry(reader).or_insert_with(|| {
            MethodState::explicit_overloads(std::slice::from_ref(&reader_signature))
        });

        if !immutable {
            let writer = MethodKey {
                owner: Some(owner.clone()),
                name: format!("{field}="),
                singleton: false,
            };
            let writer_signature = attribute_writer_signature(&reader_signature);
            self.declarations
                .accessors
                .insert(writer.clone(), AccessorKind::Writer);
            self.declarations.methods.entry(writer).or_insert_with(|| {
                MethodState::explicit_overloads(std::slice::from_ref(&writer_signature))
            });
        }

        // `prop` and `const` are DSL calls on the class object. Register a
        // permissive declaration for the DSL itself so the class body is not
        // reported as calling an unknown API while its accessors are created.
        let dsl_name = if immutable { "const" } else { "prop" };
        let dsl_key = MethodKey {
            owner: Some(owner),
            name: dsl_name.to_owned(),
            singleton: true,
        };
        let mut dsl_signature = MethodSig::new(vec![Type::Any], Type::Nil);
        dsl_signature.required_params = 0;
        dsl_signature.accepts_rest = true;
        dsl_signature.rest_index = Some(0);
        dsl_signature.accepts_keyword_rest = true;
        self.declarations.methods.entry(dsl_key).or_insert_with(|| {
            MethodState::explicit_overloads(std::slice::from_ref(&dsl_signature))
        });
    }

    fn register_class_dsl_method(&mut self, owner: &str, name: &str) {
        let key = MethodKey {
            owner: Some(owner.to_owned()),
            name: name.to_owned(),
            singleton: true,
        };
        let mut signature = MethodSig::new(vec![Type::Any], Type::Nil);
        signature.required_params = 0;
        signature.accepts_rest = true;
        signature.rest_index = Some(0);
        signature.accepts_keyword_rest = true;
        self.declarations
            .methods
            .entry(key)
            .or_insert_with(|| MethodState::explicit_overloads(std::slice::from_ref(&signature)));
    }

    fn register_class_attribute_methods(&mut self, arguments: &ruby_prism::ArgumentsNode<'_>) {
        let Some(owner) = self
            .singleton_stack
            .last()
            .cloned()
            .or_else(|| self.class_stack.last().cloned())
        else {
            return;
        };

        let mut attributes = Vec::new();
        let mut instance_accessor = None;
        let mut instance_reader = None;
        let mut instance_writer = None;
        let mut instance_predicate = None;

        for argument in &arguments.arguments() {
            if let Some(symbol) = argument.as_symbol_node() {
                attributes.push(String::from_utf8_lossy(symbol.unescaped()).into_owned());
                continue;
            }
            if let Some(string) = argument.as_string_node() {
                attributes.push(String::from_utf8_lossy(string.unescaped()).into_owned());
                continue;
            }
            let Some(keywords) = argument.as_keyword_hash_node() else {
                continue;
            };
            for element in &keywords.elements() {
                let Some(association) = element.as_assoc_node() else {
                    continue;
                };
                let Some(key) = association.key().as_symbol_node() else {
                    continue;
                };
                let name = String::from_utf8_lossy(key.unescaped());
                let value = association.value();
                let Some(value) = value
                    .as_true_node()
                    .map(|_| true)
                    .or_else(|| value.as_false_node().map(|_| false))
                else {
                    continue;
                };
                match name.as_ref() {
                    "instance_accessor" => instance_accessor = Some(value),
                    "instance_reader" => instance_reader = Some(value),
                    "instance_writer" => instance_writer = Some(value),
                    "instance_predicate" => instance_predicate = Some(value),
                    _ => {}
                }
            }
        }

        let instance_accessor = instance_accessor.unwrap_or(true);
        let instance_reader = instance_reader.unwrap_or(instance_accessor);
        let instance_writer = instance_writer.unwrap_or(instance_accessor);
        let instance_predicate = instance_predicate.unwrap_or(true);

        for attribute in attributes {
            self.register_generated_accessor(
                MethodKey {
                    owner: Some(owner.clone()),
                    name: attribute.clone(),
                    singleton: true,
                },
                AccessorKind::Reader,
            );
            self.register_generated_accessor(
                MethodKey {
                    owner: Some(owner.clone()),
                    name: format!("{attribute}="),
                    singleton: true,
                },
                AccessorKind::Writer,
            );

            if instance_reader {
                self.register_generated_accessor(
                    MethodKey {
                        owner: Some(owner.clone()),
                        name: attribute.clone(),
                        singleton: false,
                    },
                    AccessorKind::Reader,
                );
            }
            if instance_writer {
                self.register_generated_accessor(
                    MethodKey {
                        owner: Some(owner.clone()),
                        name: format!("{attribute}="),
                        singleton: false,
                    },
                    AccessorKind::Writer,
                );
            }
            if instance_predicate {
                self.register_generated_predicate(MethodKey {
                    owner: Some(owner.clone()),
                    name: format!("{attribute}?"),
                    singleton: true,
                });
                if instance_reader {
                    self.register_generated_predicate(MethodKey {
                        owner: Some(owner.clone()),
                        name: format!("{attribute}?"),
                        singleton: false,
                    });
                }
            }
        }
    }

    fn register_generated_accessor(&mut self, key: MethodKey, kind: AccessorKind) {
        self.declarations
            .accessors
            .entry(key.clone())
            .or_insert(kind);
        self.declarations
            .methods
            .entry(key)
            .or_insert_with(|| MethodState::inferred_accessor(kind));
    }

    fn register_generated_predicate(&mut self, key: MethodKey) {
        let mut state = MethodState::inferred(None);
        state.return_type = Some(Type::bool());
        self.declarations.methods.entry(key).or_insert(state);
    }

    fn register_delegate_methods(&mut self, arguments: &ruby_prism::ArgumentsNode<'_>) {
        let Some(owner) = self.current_owner() else {
            return;
        };

        let mut methods = Vec::new();
        let mut target = None;
        let mut prefix = None;
        let mut automatic_prefix = false;
        let mut private = false;

        for argument in &arguments.arguments() {
            if let Some(symbol) = argument.as_symbol_node() {
                methods.push(String::from_utf8_lossy(symbol.unescaped()).into_owned());
                continue;
            }
            if let Some(string) = argument.as_string_node() {
                methods.push(String::from_utf8_lossy(string.unescaped()).into_owned());
                continue;
            }
            let Some(keywords) = argument.as_keyword_hash_node() else {
                continue;
            };
            for element in &keywords.elements() {
                let Some(association) = element.as_assoc_node() else {
                    continue;
                };
                let Some(key) = association.key().as_symbol_node() else {
                    continue;
                };
                let key = String::from_utf8_lossy(key.unescaped());
                let value = association.value();
                match key.as_ref() {
                    "to" => {
                        target = Some(self.method_name(&value));
                    }
                    "prefix" => {
                        if let Some(symbol) = value.as_symbol_node() {
                            prefix = Some(String::from_utf8_lossy(symbol.unescaped()).into_owned());
                        } else if let Some(string) = value.as_string_node() {
                            prefix = Some(String::from_utf8_lossy(string.unescaped()).into_owned());
                        } else if value.as_true_node().is_some() {
                            automatic_prefix = true;
                        }
                    }
                    "private" => {
                        private = value.as_true_node().is_some();
                    }
                    _ => {}
                }
            }
        }
        if automatic_prefix {
            prefix = target;
        }

        for method in methods {
            let name = prefix
                .as_ref()
                .filter(|prefix| !prefix.is_empty())
                .map_or_else(|| method.clone(), |prefix| format!("{prefix}_{method}"));
            let key = MethodKey {
                owner: Some(owner.clone()),
                name,
                singleton: self.current_singleton(),
            };
            let mut state = MethodState::inferred(None);
            // Rails' generated method forwards positional, keyword, and block
            // arguments. The delegated return type depends on the runtime
            // target, so Any is the same conservative boundary as an
            // unresolved generated method body.
            state.return_type = Some(Type::Any);
            state.accepts_rest = true;
            state.rest_index = Some(0);
            state.accepts_keyword_rest = true;
            if private {
                state.visibility = Visibility::Private;
            }
            self.declarations.methods.entry(key).or_insert(state);
        }
    }
}

impl<'pr> Visit<'pr> for MethodRegistrar<'_> {
    fn visit_def_node(&mut self, node: &DefNode<'pr>) {
        let definition_start = prism::span(&node.as_node()).0;
        let key = self.definition_key(node);
        self.declarations
            .definitions
            .insert(definition_start, key.clone());
        self.declarations.parameter_shapes.insert(
            definition_start,
            ParameterShape::from_parameters(self.source, node.parameters()),
        );
        let visibility = self
            .visibility_overrides
            .get(&key)
            .copied()
            .or_else(|| self.visibility_stack.last().copied())
            .unwrap_or(Visibility::Public);
        let state = self
            .declarations
            .methods
            .entry(key)
            .or_insert_with(|| MethodState::inferred(node.parameters()));
        state.visibility = visibility;
        self.method_depth += 1;
        ruby_prism::visit_def_node(self, node);
        self.method_depth -= 1;
    }

    fn visit_class_node(&mut self, node: &ClassNode<'pr>) {
        self.report_interface_on_class(&node.as_node());
        let name = self.scope_name(&node.constant_path());
        let struct_fields = node
            .superclass()
            .and_then(|superclass| self.struct_superclass_fields(&superclass));
        let superclass = node.superclass().map(|superclass| {
            if struct_fields.is_some() {
                "Struct".to_owned()
            } else if superclass.as_self_node().is_some() {
                self.class_stack
                    .last()
                    .cloned()
                    .unwrap_or_else(|| "Object".to_owned())
            } else {
                self.scope_reference(&superclass)
            }
        });
        let info = self.declarations.classes.entry(name.clone()).or_default();
        if let Some(parameters) = self
            .class_type_parameters
            .get(&prism::span(&node.as_node()).0)
        {
            for parameter in parameters {
                if !info.type_members.contains_key(parameter) {
                    let index = info.type_members.len();
                    info.type_members
                        .insert(parameter.clone(), GenericMember { index, fixed: None });
                }
            }
        }
        if info.superclass.is_none() {
            info.superclass = superclass;
        }
        if struct_fields.is_some() {
            info.struct_fields = struct_fields;
        }
        self.class_stack.push(name);
        self.visibility_stack.push(Visibility::Public);
        let singleton_stack = std::mem::take(&mut self.singleton_stack);
        ruby_prism::visit_class_node(self, node);
        self.singleton_stack = singleton_stack;
        self.visibility_stack.pop();
        self.class_stack.pop();
    }

    fn visit_module_node(&mut self, node: &ruby_prism::ModuleNode<'pr>) {
        let name = self.scope_name(&node.constant_path());
        let required_ancestors = self.required_ancestors(&node.as_node());
        let info = self.declarations.classes.entry(name.clone()).or_default();
        info.is_module = true;
        info.requires_ancestors.extend(required_ancestors);
        self.class_stack.push(name);
        self.visibility_stack.push(Visibility::Public);
        let singleton_stack = std::mem::take(&mut self.singleton_stack);
        ruby_prism::visit_module_node(self, node);
        self.singleton_stack = singleton_stack;
        self.visibility_stack.pop();
        self.class_stack.pop();
    }

    fn visit_singleton_class_node(&mut self, node: &ruby_prism::SingletonClassNode<'pr>) {
        self.report_interface_on_class(&node.as_node());
        let owner = if node.expression().as_self_node().is_some() {
            self.class_stack
                .last()
                .cloned()
                .or_else(|| Some("Object".to_owned()))
        } else {
            let text = prism::text(self.source, &node.expression())
                .trim()
                .trim_start_matches("::")
                .to_owned();
            text.starts_with(|character: char| character.is_ascii_uppercase())
                .then_some(text)
        };
        if let Some(owner) = owner {
            self.singleton_stack.push(owner);
            self.visibility_stack.push(Visibility::Public);
            ruby_prism::visit_singleton_class_node(self, node);
            self.visibility_stack.pop();
            self.singleton_stack.pop();
        } else {
            ruby_prism::visit_singleton_class_node(self, node);
        }
    }

    fn visit_alias_method_node(&mut self, node: &ruby_prism::AliasMethodNode<'pr>) {
        if self.method_depth == 0 {
            let owner = self
                .singleton_stack
                .last()
                .cloned()
                .or_else(|| self.class_stack.last().cloned());
            let singleton = self.singleton_stack.last().is_some();
            let old_name = self.method_name(&node.old_name());
            let new_name = self.method_name(&node.new_name());
            self.declarations.aliases.insert(
                MethodKey {
                    owner: owner.clone(),
                    name: new_name,
                    singleton,
                },
                MethodKey {
                    owner,
                    name: old_name,
                    singleton,
                },
            );
        }
        ruby_prism::visit_alias_method_node(self, node);
    }

    fn visit_constant_path_write_node(&mut self, node: &ruby_prism::ConstantPathWriteNode<'pr>) {
        let target = node.target();
        let name = self.constant_assignment_name(&prism::text(self.source, &target.as_node()));
        if let Some(type_) = self
            .parse_typed_constant(&node.value())
            .or_else(|| self.inline_constant_type(&node.as_node()))
        {
            self.declarations.constants.insert(name.clone(), type_);
        } else if let Some(target) = self.constant_alias_target(&node.value()) {
            self.declarations
                .constants
                .insert(name.clone(), Self::class_object_type(&target));
        }
        self.register_type_alias(name, &node.value());
        ruby_prism::visit_constant_path_write_node(self, node);
    }

    fn visit_constant_write_node(&mut self, node: &ruby_prism::ConstantWriteNode<'pr>) {
        let constant_name = prism::constant_name(node.name());
        if let Some(owner) = self.class_stack.last() {
            if let Some(member) = self.parse_generic_member(&node.value()) {
                let info = self.declarations.classes.entry(owner.clone()).or_default();
                let index = info.type_members.len();
                info.type_members
                    .insert(constant_name.clone(), GenericMember { index, ..member });
            }
        }
        let name = self.constant_assignment_name(&constant_name);
        if let Some(type_) = self
            .parse_typed_constant(&node.value())
            .or_else(|| self.inline_constant_type(&node.as_node()))
        {
            self.declarations.constants.insert(name.clone(), type_);
        } else if let Some(target) = self.constant_alias_target(&node.value()) {
            self.declarations
                .constants
                .insert(name.clone(), Self::class_object_type(&target));
        }
        self.register_type_alias(name, &node.value());

        // `Parameter = Struct.new(:name) do ... end` creates a real class
        // whose block is a class body. Give methods declared in that block
        // the generated constant's owner so their instance bodies can be
        // checked and dispatched later.
        if let Some(fields) = self.struct_superclass_fields(&node.value()) {
            let owner = self.constant_assignment_name(&constant_name);
            let info = self.declarations.classes.entry(owner.clone()).or_default();
            info.superclass = Some("Struct".to_owned());
            info.struct_fields = Some(fields);
            self.class_stack.push(owner);
            self.visibility_stack.push(Visibility::Public);
            ruby_prism::visit_constant_write_node(self, node);
            self.visibility_stack.pop();
            self.class_stack.pop();
            return;
        }
        ruby_prism::visit_constant_write_node(self, node);
    }

    fn visit_call_node(&mut self, node: &CallNode<'pr>) {
        // Mixins are often applied from a top-level setup file rather than
        // inside the class body (`Minitest::Test.extend(TestMacro)`). Keep
        // those constant-receiver calls in the class graph so later method
        // lookup sees the same ancestors Ruby does at runtime.
        if self.method_depth == 0
            && node.receiver().is_some()
            && matches!(
                prism::constant_name(node.name()).as_str(),
                "include" | "prepend" | "extend"
            )
            && node
                .arguments()
                .is_some_and(|arguments| !arguments.arguments().is_empty())
        {
            let receiver = node.receiver().expect("receiver was checked");
            let owner = self
                .scope_reference(&receiver)
                .trim_start_matches("::")
                .to_owned();
            if owner != "self" && owner != "super" {
                let modules = node
                    .arguments()
                    .map(|arguments| {
                        arguments
                            .arguments()
                            .into_iter()
                            .map(|argument| self.scope_reference(&argument))
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                let info = self.declarations.classes.entry(owner).or_default();
                match prism::constant_name(node.name()).as_str() {
                    "include" => info.includes.extend(modules),
                    "prepend" => info.prepends.extend(modules),
                    "extend" => info.extends.extend(modules),
                    _ => unreachable!("mixin names are checked above"),
                }
            }
        }
        if self.method_depth == 0 && node.receiver().is_none() && self.class_stack.last().is_some()
        {
            let name = prism::constant_name(node.name());
            if name == "prop" || name == "const" {
                self.register_struct_property(node, name == "const");
            } else if matches!(name.as_str(), "abstract!" | "interface!")
                && node.arguments().is_none()
            {
                if let Some(owner) = self
                    .singleton_stack
                    .last()
                    .or_else(|| self.class_stack.last())
                    .cloned()
                {
                    self.register_class_dsl_method(&owner, &name);
                }
            }
            let arguments = node.arguments().map(|arguments| {
                arguments
                    .arguments()
                    .into_iter()
                    .map(|argument| self.method_name(&argument))
                    .collect::<Vec<_>>()
            });
            if name == "class_attribute" {
                if let Some(nodes) = node.arguments() {
                    self.register_class_attribute_methods(&nodes);
                }
            }
            if name == "delegate" {
                if let Some(nodes) = node.arguments() {
                    self.register_delegate_methods(&nodes);
                }
            }
            if name == "has_attached_class!" && arguments.is_none() {
                if let Some(owner) = self
                    .singleton_stack
                    .last()
                    .cloned()
                    .or_else(|| self.class_stack.last().cloned())
                {
                    let info = self.declarations.classes.entry(owner).or_default();
                    let index = info
                        .type_members
                        .get("out")
                        .map_or_else(|| info.type_members.len(), |member| member.index);
                    info.type_members
                        .entry("out".to_owned())
                        .or_insert_with(|| GenericMember { index, fixed: None });
                    info.attached_class_member = Some(index);
                }
            }
            if arguments.is_none() {
                match name.as_str() {
                    "private" => self.set_default_visibility(Visibility::Private),
                    "protected" => self.set_default_visibility(Visibility::Protected),
                    "public" => self.set_default_visibility(Visibility::Public),
                    _ => {}
                }
            }
            if let Some(arguments) = arguments {
                match name.as_str() {
                    "private" => self.set_visibility_for_method_names(
                        &arguments,
                        Visibility::Private,
                        self.current_singleton(),
                    ),
                    "protected" => self.set_visibility_for_method_names(
                        &arguments,
                        Visibility::Protected,
                        self.current_singleton(),
                    ),
                    "public" => self.set_visibility_for_method_names(
                        &arguments,
                        Visibility::Public,
                        self.current_singleton(),
                    ),
                    "private_class_method" => {
                        let owner = self.current_owner();
                        if let Some(nodes) = node.arguments() {
                            for argument in &nodes.arguments() {
                                if let Some(definition) = argument.as_def_node() {
                                    let key = self.definition_key(&definition);
                                    self.visibility_overrides.insert(key, Visibility::Private);
                                }
                            }
                        }
                        if owner.is_some() {
                            self.set_visibility_for_method_names(
                                &arguments,
                                Visibility::Private,
                                true,
                            );
                        }
                    }
                    _ => {}
                }
                if matches!(
                    name.as_str(),
                    "include" | "prepend" | "extend" | "mixes_in_class_methods"
                ) {
                    let Some(owner) = self
                        .singleton_stack
                        .last()
                        .or_else(|| self.class_stack.last())
                    else {
                        ruby_prism::visit_call_node(self, node);
                        return;
                    };
                    let modules = arguments
                        .iter()
                        .map(|module| self.scope_reference_text(module))
                        .collect::<Vec<_>>();
                    let info = self.declarations.classes.entry(owner.clone()).or_default();
                    for module in modules {
                        match name.as_str() {
                            "include" => info.includes.push(module),
                            "prepend" => info.prepends.push(module),
                            "extend" if module == "self" && info.is_module => {
                                info.extend_self = true;
                            }
                            "extend" => info.extends.push(module),
                            "mixes_in_class_methods" => info.class_methods.push(module),
                            _ => unreachable!("mixin names are checked above"),
                        }
                    }
                }
                if matches!(name.as_str(), "alias_method") && arguments.len() >= 2 {
                    let owner = self
                        .singleton_stack
                        .last()
                        .cloned()
                        .or_else(|| self.class_stack.last().cloned());
                    let singleton = self.singleton_stack.last().is_some();
                    self.declarations.aliases.insert(
                        MethodKey {
                            owner: owner.clone(),
                            name: arguments[0].clone(),
                            singleton,
                        },
                        MethodKey {
                            owner,
                            name: arguments[1].clone(),
                            singleton,
                        },
                    );
                }
                if name == "module_function" {
                    let owner = self
                        .singleton_stack
                        .last()
                        .cloned()
                        .or_else(|| self.class_stack.last().cloned());
                    if let Some(owner) = owner {
                        if let Some(nodes) = node.arguments() {
                            for argument in &nodes.arguments() {
                                let method_name = argument
                                    .as_def_node()
                                    .map(|definition| prism::constant_name(definition.name()))
                                    .unwrap_or_else(|| self.method_name(&argument));
                                self.declarations.aliases.insert(
                                    MethodKey {
                                        owner: Some(owner.clone()),
                                        name: method_name.clone(),
                                        singleton: true,
                                    },
                                    MethodKey {
                                        owner: Some(owner.clone()),
                                        name: method_name,
                                        singleton: false,
                                    },
                                );
                            }
                        }
                    }
                }
                if name == "has_attached_class!" {
                    let owner = self
                        .singleton_stack
                        .last()
                        .cloned()
                        .or_else(|| self.class_stack.last().cloned());
                    if let Some(owner) = owner {
                        let member_name = arguments
                            .first()
                            .cloned()
                            .unwrap_or_else(|| "out".to_owned());
                        let info = self.declarations.classes.entry(owner).or_default();
                        let index = info
                            .type_members
                            .get(&member_name)
                            .map_or(info.type_members.len(), |member| member.index);
                        info.type_members
                            .entry(member_name)
                            .or_insert_with(|| GenericMember { index, fixed: None });
                        info.attached_class_member = Some(index);
                    }
                }
                if matches!(
                    name.as_str(),
                    "attr_reader" | "attr_writer" | "attr_accessor"
                ) {
                    self.register_accessor_call(node);
                }
            }
        }
        if self.method_depth == 0
            && node.receiver().is_some()
            && matches!(
                prism::constant_name(node.name()).as_str(),
                "attr_reader" | "attr_writer" | "attr_accessor"
            )
        {
            self.register_accessor_call(node);
        }
        let dynamic_definition_target = self.dynamic_definition_target(node);
        if let Some(target) = dynamic_definition_target.as_ref() {
            self.dynamic_definition_stack.push(target.clone());
        }
        ruby_prism::visit_call_node(self, node);
        if dynamic_definition_target.is_some() {
            self.dynamic_definition_stack.pop();
        }
    }
}

impl MethodRegistrar<'_> {
    fn definition_key<'node>(&self, node: &DefNode<'node>) -> MethodKey {
        let name = prism::constant_name(node.name());
        if let Some((owner, singleton)) = self.dynamic_definition_stack.last() {
            if node.receiver().is_none() {
                return MethodKey {
                    owner: Some(owner.clone()),
                    name,
                    singleton: *singleton,
                };
            }
        }
        if let Some(receiver) = node.receiver() {
            let owner = if receiver.as_self_node().is_some() {
                self.class_stack.last().cloned()
            } else {
                Some(
                    prism::text(self.source, &receiver)
                        .trim_start_matches("::")
                        .to_owned(),
                )
            };
            MethodKey {
                owner,
                name,
                singleton: true,
            }
        } else if let Some(owner) = self.singleton_stack.last() {
            MethodKey {
                owner: Some(owner.clone()),
                name,
                singleton: true,
            }
        } else if let Some(owner) = self.class_stack.last() {
            MethodKey {
                owner: Some(owner.clone()),
                name,
                singleton: false,
            }
        } else {
            MethodKey::top_level(name)
        }
    }

    fn dynamic_definition_target<'node>(&self, node: &CallNode<'node>) -> Option<(String, bool)> {
        if self.method_depth != 0
            || !node
                .block()
                .is_some_and(|block| block.as_block_node().is_some())
            || !matches!(
                prism::constant_name(node.name()).as_str(),
                "class_eval" | "module_eval" | "class_exec" | "instance_eval"
            )
        {
            return None;
        }
        let owner = node
            .receiver()
            .map(|receiver| self.scope_reference(&receiver))
            .filter(|owner| owner != "self" && owner != "super")
            .or_else(|| {
                self.singleton_stack
                    .last()
                    .cloned()
                    .or_else(|| self.class_stack.last().cloned())
            })?;
        let singleton = prism::constant_name(node.name()) == "instance_eval";
        Some((owner, singleton))
    }

    fn current_owner(&self) -> Option<String> {
        self.singleton_stack
            .last()
            .cloned()
            .or_else(|| self.class_stack.last().cloned())
    }

    fn current_singleton(&self) -> bool {
        self.singleton_stack.last().is_some()
    }

    fn accessor_owner<'node>(&self, node: &CallNode<'node>) -> (Option<String>, bool) {
        let receiver_is_singleton_class = node.receiver().is_some_and(|receiver| {
            receiver.as_call_node().is_some_and(|call| {
                call.receiver().is_none() && prism::constant_name(call.name()) == "singleton_class"
            })
        });
        if receiver_is_singleton_class {
            (self.class_stack.last().cloned(), true)
        } else {
            (
                self.singleton_stack
                    .last()
                    .cloned()
                    .or_else(|| self.class_stack.last().cloned()),
                self.singleton_stack.last().is_some(),
            )
        }
    }

    fn register_accessor_call<'node>(&mut self, node: &CallNode<'node>) {
        let Some(nodes) = node.arguments() else {
            return;
        };
        let name = prism::constant_name(node.name());
        let arguments = nodes
            .arguments()
            .into_iter()
            .map(|argument| self.method_name(&argument))
            .collect::<Vec<_>>();
        let (owner, singleton) = self.accessor_owner(node);
        let signatures = self
            .attribute_annotations
            .get(&prism::span(&node.as_node()).0);
        for attribute in arguments {
            let add_accessor = |registrar: &mut Self, name: String, kind: AccessorKind| {
                let key = MethodKey {
                    owner: owner.clone(),
                    name,
                    singleton,
                };
                registrar.declarations.accessors.insert(key.clone(), kind);
                let state = signatures.map_or_else(
                    || MethodState::inferred_accessor(kind),
                    |signatures| {
                        let signatures = if kind == AccessorKind::Writer {
                            signatures
                                .iter()
                                .map(attribute_writer_signature)
                                .collect::<Vec<_>>()
                        } else {
                            signatures.clone()
                        };
                        MethodState::explicit_overloads(&signatures)
                    },
                );
                registrar.declarations.methods.entry(key).or_insert(state);
            };
            match name.as_str() {
                "attr_reader" => add_accessor(self, attribute, AccessorKind::Reader),
                "attr_writer" => {
                    add_accessor(self, format!("{}=", attribute), AccessorKind::Writer)
                }
                "attr_accessor" => {
                    add_accessor(self, attribute.clone(), AccessorKind::Reader);
                    add_accessor(self, format!("{}=", attribute), AccessorKind::Writer);
                }
                _ => {}
            }
        }
    }

    fn set_visibility_for_method_names(
        &mut self,
        names: &[String],
        visibility: Visibility,
        singleton: bool,
    ) {
        let Some(owner) = self.current_owner() else {
            return;
        };
        for name in names {
            let key = MethodKey {
                owner: Some(owner.clone()),
                name: name.clone(),
                singleton,
            };
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                state.visibility = visibility;
            }
        }
    }

    fn set_default_visibility(&mut self, visibility: Visibility) {
        if let Some(current) = self.visibility_stack.last_mut() {
            *current = visibility;
        }
    }

    fn required_ancestors<'node>(&self, node: &Node<'node>) -> Vec<String> {
        let mut result = Vec::new();
        self.for_each_preceding_comment_line(node, |line| {
            if let Some(value) = line.strip_prefix(b"# @requires_ancestor:") {
                let value = String::from_utf8_lossy(value);
                let value = value.trim();
                if !value.is_empty() {
                    result.push(value.to_owned());
                }
            }
            true
        });
        result.reverse();
        result
    }

    fn scope_name<'node>(&self, node: &Node<'node>) -> String {
        let raw = prism::text(self.source, node);
        let absolute = raw.starts_with("::");
        let raw = raw.trim_start_matches("::");
        let Some(scope) = self.class_stack.last() else {
            return raw.to_owned();
        };
        if absolute {
            return raw.to_owned();
        }
        if !raw.contains("::") {
            return format!("{scope}::{raw}");
        }

        // A qualified class declaration is still relative to the current
        // lexical scope (`module LSP; class Error::Diagnostics; end; end`).
        // Keep an already-qualified path intact and otherwise qualify a path
        // whose first component is known in the current scope.
        if raw == scope || raw.starts_with(&format!("{scope}::")) {
            return raw.to_owned();
        }
        let first = raw.split("::").next().unwrap_or(raw);
        let nested_first = format!("{scope}::{first}");
        if self.declarations.classes.contains_key(&nested_first)
            || self.declarations.constants.contains_key(&nested_first)
        {
            format!("{scope}::{raw}")
        } else if self.declarations.classes.contains_key(raw)
            || self.declarations.constants.contains_key(raw)
        {
            raw.to_owned()
        } else {
            format!("{scope}::{raw}")
        }
    }

    fn method_name<'node>(&self, node: &Node<'node>) -> String {
        let text = prism::text(self.source, node).trim().to_owned();
        text.trim_start_matches(':')
            .trim_matches('"')
            .trim_matches('\'')
            .to_owned()
    }

    fn scope_reference<'node>(&self, node: &Node<'node>) -> String {
        self.scope_reference_text(&prism::text(self.source, node))
    }

    fn struct_superclass_fields<'node>(&self, node: &Node<'node>) -> Option<Vec<String>> {
        let call = node.as_call_node()?;
        if prism::constant_name(call.name()) != "new" {
            return None;
        }
        let receiver = call.receiver()?;
        let receiver_text = prism::text(self.source, &receiver);
        let receiver_name = receiver_text.trim().trim_start_matches("::");
        if receiver_name != "Struct" {
            return None;
        }
        Some(
            call.arguments()
                .map(|arguments| {
                    arguments
                        .arguments()
                        .into_iter()
                        .filter_map(|argument| {
                            argument.as_symbol_node().map(|symbol| {
                                String::from_utf8_lossy(symbol.unescaped()).into_owned()
                            })
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default(),
        )
    }

    fn scope_reference_text(&self, text: &str) -> String {
        let absolute = text.trim_start().starts_with("::");
        let raw = text.trim().trim_start_matches("::");
        if absolute {
            // Keep the root marker until name resolution. Without it,
            // `class Parser::AST::Node < ::AST::Node` can resolve its
            // superclass back to itself when `Parser::AST::Node` is also a
            // known lexical candidate.
            format!("::{raw}")
        } else if raw.contains("::") || self.class_stack.is_empty() {
            raw.to_owned()
        } else {
            let candidate = format!(
                "{}::{raw}",
                self.class_stack.last().expect("stack is not empty")
            );
            if self.declarations.classes.contains_key(&candidate) {
                candidate
            } else {
                raw.to_owned()
            }
        }
    }

    fn constant_assignment_name(&self, text: &str) -> String {
        let absolute = text.trim_start().starts_with("::");
        let raw = text.trim().trim_start_matches("::");
        if absolute || raw.contains("::") || self.class_stack.is_empty() {
            raw.to_owned()
        } else {
            format!(
                "{}::{raw}",
                self.class_stack.last().expect("stack is not empty")
            )
        }
    }

    fn register_type_alias<'node>(&mut self, name: String, value: &Node<'node>) {
        if let Some(type_) = signature::parse_sorbet_type_alias(&prism::text(self.source, value)) {
            self.declarations.type_aliases.insert(name, type_);
        }
    }

    fn parse_typed_constant<'node>(&self, value: &Node<'node>) -> Option<Type> {
        let call = value.as_call_node()?;
        if prism::constant_name(call.name()) != "let"
            || call
                .receiver()
                .is_none_or(|receiver| prism::text(self.source, &receiver).trim() != "T")
        {
            return None;
        }
        call.arguments()?
            .arguments()
            .into_iter()
            .nth(1)
            .map(|argument| signature::parse_type(&prism::text(self.source, &argument)))
    }

    /// RBI files commonly expose a standard-library namespace through a
    /// constant alias (`YAML = Psych`). RBI bodies are declaration input and
    /// are not executed during inference, so retain the class-object identity
    /// of a statically named RHS while registering the constant.
    fn constant_alias_target<'node>(&self, value: &Node<'node>) -> Option<String> {
        let value_text = prism::text(self.source, value);
        let text = value_text.trim();
        let target = text.strip_prefix("::").unwrap_or(text);
        (!target.is_empty()
            && target.split("::").all(|part| {
                !part.is_empty()
                    && part.as_bytes()[0].is_ascii_uppercase()
                    && part
                        .bytes()
                        .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            }))
        .then(|| target.to_owned())
    }

    fn class_object_type(target: &str) -> Type {
        Type::Named("Class".to_owned(), vec![Type::named(target)])
    }

    fn parse_generic_member<'node>(&self, value: &Node<'node>) -> Option<GenericMember> {
        let call = value.as_call_node()?;
        let name = prism::constant_name(call.name());
        if !matches!(name.as_str(), "type_member" | "type_template") {
            return None;
        }
        let text = prism::text(self.source, value);
        let fixed = text
            .split_once("fixed:")
            .and_then(|(_, rest)| rest.split('}').next())
            .map(str::trim)
            .filter(|type_| !type_.is_empty())
            .map(signature::parse_type);
        Some(GenericMember { index: 0, fixed })
    }
}
