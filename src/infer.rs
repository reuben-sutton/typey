use crate::diagnostic::Diagnostic;
use crate::prism;
use crate::signature::{self, AnnotationTable, AssertionKind, MethodSig};
use crate::types::{Type, TypeLattice};
use ruby_prism::{CallNode, DefNode, IfNode, Node, ParametersNode, UnlessNode};
use std::collections::BTreeMap;

/// How much file-mode metadata the checker should use. Typey is intentionally
/// permissive for untyped Ruby, while explicit annotations remain checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strictness {
    Ignore,
    Strict,
    Strong,
}

/// Configuration for one check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckerConfig {
    pub strictness: Strictness,
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            strictness: Strictness::Ignore,
        }
    }
}

/// A type recorded for an expression, useful to editors and debugging tools.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferredType {
    pub start: usize,
    pub end: usize,
    pub type_: Type,
}

/// The result of checking one source buffer.
#[derive(Clone, Debug, Default)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub types: Vec<InferredType>,
}

impl CheckResult {
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == crate::diagnostic::Severity::Error)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Environment {
    locals: BTreeMap<String, Type>,
}

impl Environment {
    #[must_use]
    pub fn get(&self, name: &str) -> Type {
        self.locals.get(name).cloned().unwrap_or(Type::Any)
    }

    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.locals.contains_key(name)
    }

    pub fn bind(&mut self, name: impl Into<String>, type_: Type) {
        self.locals.insert(name.into(), type_);
    }

    /// Join two control-flow environments using the same type lattice as
    /// expression inference. A local which exists on only one path can be
    /// `nil` when the other path is taken.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let lattice = TypeLattice;
        let mut result = Self::default();
        for name in self.locals.keys().chain(other.locals.keys()) {
            if result.locals.contains_key(name) {
                continue;
            }
            let type_ = match (self.locals.get(name), other.locals.get(name)) {
                (Some(left), Some(right)) => lattice.join(left, right),
                (Some(value), None) | (None, Some(value)) => lattice.join(value, &Type::Nil),
                (None, None) => Type::Any,
            };
            result.locals.insert(name.clone(), type_);
        }
        result
    }

    #[must_use]
    pub fn narrowed(&self, name: &str, type_: Type) -> Self {
        let mut result = self.clone();
        result.bind(name.to_owned(), self.get(name).meet(&type_));
        result
    }
}

#[derive(Clone, Debug)]
struct Eval {
    type_: Type,
    terminated: bool,
}

struct CallSite<'a, 'node> {
    argument_nodes: &'a [Node<'node>],
    argument_types: &'a [Type],
    block: Option<&'a Node<'node>>,
}

impl Eval {
    fn value(type_: Type) -> Self {
        Self {
            type_,
            terminated: false,
        }
    }

    fn returned(type_: Type) -> Self {
        Self {
            type_,
            terminated: true,
        }
    }
}

/// Check a source buffer with direct ruby-prism parsing.
#[must_use]
pub fn check(source: &str, config: CheckerConfig) -> CheckResult {
    let bytes = source.as_bytes();
    let parsed = prism::parse(bytes);
    let annotations = signature::collect(source);
    let diagnostics = parsed
        .errors()
        .map(|error| {
            let location = error.location();
            let (start, end) = prism::location_span(&location);
            Diagnostic::error(bytes, error.message(), start, end)
        })
        .collect::<Vec<_>>();
    let analyzer = Analyzer {
        source: bytes,
        annotations,
        config,
        methods: BTreeMap::new(),
        diagnostics,
        types: Vec::new(),
    };
    let root = parsed.node();
    analyzer.run(&root)
}

struct Analyzer<'src> {
    source: &'src [u8],
    annotations: AnnotationTable,
    config: CheckerConfig,
    methods: BTreeMap<String, MethodSig>,
    diagnostics: Vec<Diagnostic>,
    types: Vec<InferredType>,
}

impl<'src> Analyzer<'src> {
    fn run<'node>(mut self, root: &Node<'node>) -> CheckResult {
        self.methods = self.annotations.methods.clone();
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);

        // Strictness is deliberately a policy hook for now. The lattice and
        // explicit annotations are shared by all modes; stronger policies can
        // add diagnostics here without changing the inference engine.
        let _strictness = self.config.strictness;
        self.diagnostics.sort_by(|left, right| {
            left.start
                .cmp(&right.start)
                .then_with(|| left.message.cmp(&right.message))
        });
        CheckResult {
            diagnostics: self.diagnostics,
            types: self.types,
        }
    }

    fn record<'node>(&mut self, node: &Node<'node>, type_: Type) -> Type {
        let (start, end) = prism::span(node);
        self.types.push(InferredType {
            start,
            end,
            type_: type_.clone(),
        });
        type_
    }

    fn error<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        let (start, end) = prism::span(node);
        self.diagnostics
            .push(Diagnostic::error(self.source, message, start, end));
    }

    fn note<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        let (start, end) = prism::span(node);
        self.diagnostics
            .push(Diagnostic::note(self.source, message, start, end));
    }

    fn eval_node<'node>(&mut self, node: &Node<'node>, environment: &mut Environment) -> Eval {
        if let Some(program) = node.as_program_node() {
            let result = self.eval_statements(&program.statements(), environment);
            return Eval {
                type_: self.record(node, result.type_),
                terminated: result.terminated,
            };
        }
        if let Some(statements) = node.as_statements_node() {
            let result = self.eval_statements(&statements, environment);
            return Eval {
                type_: self.record(node, result.type_),
                terminated: result.terminated,
            };
        }
        if let Some(definition) = node.as_def_node() {
            return self.eval_definition(node, &definition, environment);
        }
        if let Some(class) = node.as_class_node() {
            if let Some(body) = class.body() {
                let mut class_environment = environment.clone();
                self.eval_node(&body, &mut class_environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(module) = node.as_module_node() {
            if let Some(body) = module.body() {
                let mut module_environment = environment.clone();
                self.eval_node(&body, &mut module_environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(write) = node.as_local_variable_write_node() {
            let value_node = write.value();
            let actual = self.eval_node(&value_node, environment).type_;
            let type_ = self.apply_inline_assertion(node, actual);
            environment.bind(prism::constant_name(write.name()), type_.clone());
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_local_variable_read_node() {
            let actual = environment.get(&prism::constant_name(read.name()));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(constant) = node.as_constant_read_node() {
            let actual = signature::parse_type(&prism::constant_name(constant.name()));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(path) = node.as_constant_path_node() {
            let actual = signature::parse_type(&self.constant_path_name(&path));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if node.as_self_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Object);
            return Eval::value(self.record(node, type_));
        }
        if let Some(integer) = node.as_integer_node() {
            let _ = integer.value();
            let type_ = self.apply_inline_assertion(node, Type::Integer);
            return Eval::value(self.record(node, type_));
        }
        if node.as_float_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Float);
            return Eval::value(self.record(node, type_));
        }
        if node.as_string_node().is_some() || node.as_interpolated_string_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if node.as_symbol_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Symbol);
            return Eval::value(self.record(node, type_));
        }
        if node.as_nil_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Nil);
            return Eval::value(self.record(node, type_));
        }
        if node.as_true_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::True);
            return Eval::value(self.record(node, type_));
        }
        if node.as_false_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::False);
            return Eval::value(self.record(node, type_));
        }
        if let Some(array) = node.as_array_node() {
            let mut element = Type::Never;
            for child in &array.elements() {
                let child_type = self.eval_node(&child, environment).type_;
                element = element.join(&child_type);
            }
            let element = if element.is_never() {
                Type::Any
            } else {
                element
            };
            let type_ = self.apply_inline_assertion(node, Type::Array(Box::new(element)));
            return Eval::value(self.record(node, type_));
        }
        if let Some(hash) = node.as_hash_node() {
            let mut key = Type::Never;
            let mut value = Type::Never;
            for child in &hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    let key_type = self.eval_node(&assoc.key(), environment).type_;
                    let value_type = self.eval_node(&assoc.value(), environment).type_;
                    key = key.join(&key_type);
                    value = value.join(&value_type);
                } else {
                    self.eval_node(&child, environment);
                }
            }
            let key = if key.is_never() { Type::Any } else { key };
            let value = if value.is_never() { Type::Any } else { value };
            let type_ =
                self.apply_inline_assertion(node, Type::Hash(Box::new(key), Box::new(value)));
            return Eval::value(self.record(node, type_));
        }
        if let Some(keyword_hash) = node.as_keyword_hash_node() {
            let mut key = Type::Never;
            let mut value = Type::Never;
            for child in &keyword_hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    key = key.join(&self.eval_node(&assoc.key(), environment).type_);
                    value = value.join(&self.eval_node(&assoc.value(), environment).type_);
                }
            }
            let key = if key.is_never() { Type::Any } else { key };
            let value = if value.is_never() { Type::Any } else { value };
            let type_ =
                self.apply_inline_assertion(node, Type::Hash(Box::new(key), Box::new(value)));
            return Eval::value(self.record(node, type_));
        }
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                let result = self.eval_node(&body, environment);
                let type_ = self.apply_inline_assertion(node, result.type_.clone());
                return Eval {
                    type_: self.record(node, type_),
                    terminated: result.terminated,
                };
            }
            let type_ = self.apply_inline_assertion(node, Type::Nil);
            return Eval::value(self.record(node, type_));
        }
        if let Some(begin) = node.as_begin_node() {
            let mut result = Eval::value(Type::Nil);
            if let Some(statements) = begin.statements() {
                result = self.eval_statements(&statements, environment);
            }
            if let Some(rescue) = begin.rescue_clause() {
                let mut rescue_environment = environment.clone();
                if let Some(rescue_statements) = rescue.statements() {
                    let rescue_result =
                        self.eval_statements(&rescue_statements, &mut rescue_environment);
                    result.type_ = result.type_.join(&rescue_result.type_);
                    result.terminated &= rescue_result.terminated;
                }
                *environment = environment.join(&rescue_environment);
            }
            if let Some(else_clause) = begin.else_clause() {
                if let Some(statements) = else_clause.statements() {
                    result = self.eval_statements(&statements, environment);
                }
            }
            let type_ = self.apply_inline_assertion(node, result.type_);
            return Eval {
                type_: self.record(node, type_),
                terminated: result.terminated,
            };
        }
        if let Some(if_node) = node.as_if_node() {
            return self.eval_if(node, &if_node, environment);
        }
        if let Some(unless) = node.as_unless_node() {
            return self.eval_unless(node, &unless, environment);
        }
        if let Some(and) = node.as_and_node() {
            let left_node = and.left();
            let left = self.eval_node(&left_node, environment).type_;
            let mut right_environment = environment.clone();
            self.narrow_from_predicate(&left_node, &mut right_environment, true);
            let right_node = and.right();
            let right = self.eval_node(&right_node, &mut right_environment).type_;
            let type_ = self.apply_inline_assertion(node, Type::union([left.falsy_part(), right]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(or) = node.as_or_node() {
            let left_node = or.left();
            let left = self.eval_node(&left_node, environment).type_;
            let mut right_environment = environment.clone();
            self.narrow_from_predicate(&left_node, &mut right_environment, false);
            let right_node = or.right();
            let right = self.eval_node(&right_node, &mut right_environment).type_;
            let type_ = self.apply_inline_assertion(node, Type::union([left.truthy_part(), right]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(return_node) = node.as_return_node() {
            let type_ = if let Some(arguments) = return_node.arguments() {
                let mut result = Type::Nil;
                for argument in &arguments.arguments() {
                    result = self.eval_node(&argument, environment).type_;
                }
                result
            } else {
                Type::Nil
            };
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::returned(self.record(node, type_));
        }
        if let Some(call) = node.as_call_node() {
            let actual = self.eval_call(node, &call, environment);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(block) = node.as_block_node() {
            let block_type = self.eval_block(&block, &[], environment).type_;
            let type_ = self.apply_inline_assertion(node, block_type);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(splat) = node.as_splat_node() {
            let type_ = splat
                .expression()
                .map_or(Type::Any, |value| self.eval_node(&value, environment).type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(while_node) = node.as_while_node() {
            let predicate = while_node.predicate();
            self.eval_node(&predicate, environment);
            if let Some(statements) = while_node.statements() {
                let mut loop_environment = environment.clone();
                self.narrow_from_predicate(&predicate, &mut loop_environment, true);
                self.eval_node(&statements.as_node(), &mut loop_environment);
                *environment = environment.join(&loop_environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::Nil);
            return Eval::value(self.record(node, type_));
        }
        if let Some(until_node) = node.as_until_node() {
            let predicate = until_node.predicate();
            self.eval_node(&predicate, environment);
            if let Some(statements) = until_node.statements() {
                let mut loop_environment = environment.clone();
                self.narrow_from_predicate(&predicate, &mut loop_environment, false);
                self.eval_node(&statements.as_node(), &mut loop_environment);
                *environment = environment.join(&loop_environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::Nil);
            return Eval::value(self.record(node, type_));
        }

        let type_ = self.apply_inline_assertion(node, Type::Any);
        Eval::value(self.record(node, type_))
    }

    fn eval_statements<'node>(
        &mut self,
        statements: &ruby_prism::StatementsNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let mut last = Type::Nil;
        let mut terminated = false;
        let body = statements.body();
        for child in &body {
            let result = self.eval_node(&child, environment);
            last = result.type_;
            terminated = result.terminated;
            if terminated {
                break;
            }
        }
        Eval {
            type_: last,
            terminated,
        }
    }

    fn eval_definition<'node>(
        &mut self,
        node: &Node<'node>,
        definition: &DefNode<'node>,
        outer: &mut Environment,
    ) -> Eval {
        let name = prism::constant_name(definition.name());
        let signature = self
            .annotations
            .methods
            .get(&name)
            .cloned()
            .or_else(|| self.methods.get(&name).cloned());
        let mut method_environment = Environment::default();
        self.bind_parameters(
            definition.parameters(),
            signature.as_ref(),
            &mut method_environment,
        );

        let body_result = if let Some(body) = definition.body() {
            self.eval_node(&body, &mut method_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let inferred_return = body_result.type_.clone();
        let final_signature = if let Some(expected) = signature {
            if !inferred_return.is_never() && !inferred_return.is_subtype_of(&expected.return_type)
            {
                self.error(
                    node,
                    format!(
                        "Expected method `{name}` to return `{}`, but found `{}`",
                        expected.return_type, inferred_return
                    ),
                );
            }
            expected
        } else {
            let params = self.parameter_types(definition.parameters());
            MethodSig::new(params, inferred_return)
        };
        self.methods.insert(name, final_signature);
        let _ = outer;
        Eval::value(self.record(node, Type::Nil))
    }

    fn parameter_types<'node>(&self, parameters: Option<ParametersNode<'node>>) -> Vec<Type> {
        let Some(parameters) = parameters else {
            return Vec::new();
        };
        let mut result = Vec::new();
        for _ in &parameters.requireds() {
            result.push(Type::Any);
        }
        for _ in &parameters.optionals() {
            result.push(Type::Any);
        }
        for _ in &parameters.posts() {
            result.push(Type::Any);
        }
        result
    }

    fn bind_parameters<'node>(
        &mut self,
        parameters: Option<ParametersNode<'node>>,
        signature: Option<&MethodSig>,
        environment: &mut Environment,
    ) {
        let Some(parameters) = parameters else { return };
        let mut index = 0;
        for parameter in &parameters.requireds() {
            if let Some(required) = parameter.as_required_parameter_node() {
                self.bind_parameter(environment, required.name(), signature, index);
                index += 1;
            }
        }
        for parameter in &parameters.optionals() {
            if let Some(optional) = parameter.as_optional_parameter_node() {
                self.bind_parameter(environment, optional.name(), signature, index);
                index += 1;
            }
        }
        if let Some(rest) = parameters
            .rest()
            .and_then(|node| node.as_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                self.bind_parameter(environment, name, signature, index);
            }
            index += 1;
        }
        for parameter in &parameters.posts() {
            if let Some(post) = parameter.as_required_parameter_node() {
                self.bind_parameter(environment, post.name(), signature, index);
                index += 1;
            }
        }
        for parameter in &parameters.keywords() {
            if let Some(required) = parameter.as_required_keyword_parameter_node() {
                self.bind_parameter(environment, required.name(), signature, index);
                index += 1;
            } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                self.bind_parameter(environment, optional.name(), signature, index);
                index += 1;
            }
        }
        if let Some(rest) = parameters
            .keyword_rest()
            .and_then(|node| node.as_keyword_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                environment.bind(
                    prism::constant_name(name),
                    Type::Hash(Box::new(Type::Symbol), Box::new(Type::Any)),
                );
            }
        }
        if let Some(block) = parameters.block() {
            if let Some(name) = block.name() {
                environment.bind(
                    prism::constant_name(name),
                    Type::Proc(Vec::new(), Box::new(Type::Any)),
                );
            }
        }
    }

    fn bind_parameter<'node>(
        &self,
        environment: &mut Environment,
        name: ruby_prism::ConstantId<'node>,
        signature: Option<&MethodSig>,
        index: usize,
    ) {
        let type_ = signature
            .and_then(|signature| signature.params.get(index))
            .cloned()
            .unwrap_or(Type::Any);
        environment.bind(prism::constant_name(name), type_);
    }

    fn eval_if<'node>(
        &mut self,
        node: &Node<'node>,
        if_node: &IfNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = if_node.predicate();
        self.eval_node(&predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut then_environment, true);
        let then_result = if let Some(statements) = if_node.statements() {
            self.eval_statements(&statements, &mut then_environment)
        } else {
            Eval::value(Type::Nil)
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut else_environment, false);
        let else_result = if let Some(subsequent) = if_node.subsequent() {
            self.eval_alternative(&subsequent, &mut else_environment)
        } else {
            Eval::value(Type::Nil)
        };

        *environment = self.join_branch_environments(
            &then_environment,
            then_result.terminated,
            &else_environment,
            else_result.terminated,
        );
        let type_ =
            self.apply_inline_assertion(node, Type::union([then_result.type_, else_result.type_]));
        Eval {
            type_: self.record(node, type_),
            terminated: then_result.terminated && else_result.terminated,
        }
    }

    fn eval_unless<'node>(
        &mut self,
        node: &Node<'node>,
        unless: &UnlessNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = unless.predicate();
        self.eval_node(&predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut then_environment, false);
        let then_result = if let Some(statements) = unless.statements() {
            self.eval_statements(&statements, &mut then_environment)
        } else {
            Eval::value(Type::Nil)
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut else_environment, true);
        let else_result = if let Some(else_clause) = unless.else_clause() {
            if let Some(statements) = else_clause.statements() {
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            Eval::value(Type::Nil)
        };

        *environment = self.join_branch_environments(
            &then_environment,
            then_result.terminated,
            &else_environment,
            else_result.terminated,
        );
        let type_ =
            self.apply_inline_assertion(node, Type::union([then_result.type_, else_result.type_]));
        Eval {
            type_: self.record(node, type_),
            terminated: then_result.terminated && else_result.terminated,
        }
    }

    fn eval_alternative<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if let Some(if_node) = node.as_if_node() {
            return self.eval_if(node, &if_node, environment);
        }
        if let Some(unless) = node.as_unless_node() {
            return self.eval_unless(node, &unless, environment);
        }
        if let Some(else_clause) = node.as_else_node() {
            if let Some(statements) = else_clause.statements() {
                return self.eval_statements(&statements, environment);
            }
        }
        self.eval_node(node, environment)
    }

    fn join_branch_environments(
        &self,
        left: &Environment,
        left_terminated: bool,
        right: &Environment,
        right_terminated: bool,
    ) -> Environment {
        match (left_terminated, right_terminated) {
            (true, false) => right.clone(),
            (false, true) => left.clone(),
            _ => left.join(right),
        }
    }

    /// Refine a local using the lattice's greatest-lower-bound operation.
    /// This is intentionally a small, explicit refinement hook: adding a new
    /// predicate should not require changing the rest of inference.
    fn narrow_from_predicate<'node>(
        &self,
        node: &Node<'node>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            let current = environment.get(&name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(name, current.meet(&narrowed));
            return;
        }
        if let Some(call) = node.as_call_node() {
            let name = prism::constant_name(call.name());
            let receiver = call.receiver();
            if let Some(receiver) = receiver {
                if let Some(local) = receiver.as_local_variable_read_node() {
                    let local_name = prism::constant_name(local.name());
                    let current = environment.get(&local_name);
                    let arguments = call
                        .arguments()
                        .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                        .unwrap_or_default();
                    let narrowed = match name.as_str() {
                        "nil?" => {
                            if truthy {
                                current.meet(&Type::Nil)
                            } else {
                                current.without(&Type::Nil)
                            }
                        }
                        "is_a?" | "kind_of?" | "instance_of?" if !arguments.is_empty() => {
                            let expected =
                                signature::parse_type(&prism::text(self.source, &arguments[0]));
                            if truthy {
                                current.meet(&expected)
                            } else {
                                current.without(&expected)
                            }
                        }
                        _ => return,
                    };
                    environment.bind(local_name, narrowed);
                }
            }
        }
    }

    fn eval_call<'node>(
        &mut self,
        node: &Node<'node>,
        call: &CallNode<'node>,
        environment: &mut Environment,
    ) -> Type {
        let name = prism::constant_name(call.name());
        let argument_nodes = call
            .arguments()
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        let argument_types = argument_nodes
            .iter()
            .map(|argument| self.eval_node(argument, environment).type_)
            .collect::<Vec<_>>();
        let receiver_node = call.receiver();
        let receiver_type = receiver_node.as_ref().map_or(Type::Object, |receiver| {
            self.eval_node(receiver, environment).type_
        });

        if receiver_node
            .as_ref()
            .is_some_and(|receiver| self.constant_reference_name(receiver).as_deref() == Some("T"))
        {
            return self.eval_t_call(node, &name, &argument_nodes, &argument_types, environment);
        }

        if receiver_node.is_none() {
            if let Some(signature) = self.methods.get(&name).cloned() {
                return self.invoke_signature(
                    node,
                    &name,
                    &signature,
                    &argument_nodes,
                    &argument_types,
                );
            }
            return self.eval_global_call(
                node,
                &name,
                &argument_nodes,
                &argument_types,
                environment,
            );
        }

        let block = call.block();
        let site = CallSite {
            argument_nodes: &argument_nodes,
            argument_types: &argument_types,
            block: block.as_ref(),
        };
        let result = self.eval_method_call(&receiver_type, &name, &site, environment);
        if call.is_safe_navigation() && !receiver_type.is_any() {
            Type::union([Type::Nil, result])
        } else {
            result
        }
    }

    fn eval_t_call<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        argument_nodes: &[Node<'node>],
        argument_types: &[Type],
        environment: &mut Environment,
    ) -> Type {
        match name {
            "reveal_type" => {
                if let Some(type_) = argument_types.first() {
                    if let Some(argument) = argument_nodes.first() {
                        self.note(argument, format!("Revealed type: `{type_}`"));
                    }
                    type_.clone()
                } else {
                    self.error(node, "T.reveal_type requires one argument");
                    Type::Any
                }
            }
            "let" | "cast" | "assert_type!" | "bind" => {
                let actual = argument_types.first().cloned().unwrap_or(Type::Any);
                let expected = argument_nodes
                    .get(1)
                    .map_or(Type::Any, |argument| self.type_from_node(argument));
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
            "absurd" => {
                let actual = argument_types.first().cloned().unwrap_or(Type::Any);
                if !actual.is_never() {
                    self.error(node, format!("Expected `T.noreturn`, but found `{actual}`"));
                }
                Type::Never
            }
            "nilable" => argument_types
                .first()
                .cloned()
                .map_or(Type::Any, |type_| Type::union([Type::Nil, type_])),
            "any" => Type::union(argument_types.iter().cloned()),
            "all" => Type::intersection(argument_types.iter().cloned()),
            "noreturn" => Type::Never,
            _ => {
                let _ = environment;
                Type::Any
            }
        }
    }

    fn eval_global_call<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        argument_nodes: &[Node<'node>],
        argument_types: &[Type],
        environment: &mut Environment,
    ) -> Type {
        match name {
            "puts" | "print" | "p" | "pp" | "warn" => Type::Nil,
            "raise" | "fail" | "abort" => Type::Never,
            "Integer" => Type::Integer,
            "Float" => Type::Float,
            "String" => Type::String,
            "Symbol" => Type::Symbol,
            "Array" => argument_types.first().map_or_else(
                || Type::Array(Box::new(Type::Any)),
                |type_| match type_ {
                    Type::Array(_) => type_.clone(),
                    _ => Type::Array(Box::new(Type::Any)),
                },
            ),
            "Hash" => Type::Hash(Box::new(Type::Any), Box::new(Type::Any)),
            "lambda" | "proc" => Type::Proc(Vec::new(), Box::new(Type::Any)),
            "rand" => Type::Float,
            "sleep" => Type::Integer,
            _ => {
                let _ = (node, argument_nodes, environment);
                Type::Any
            }
        }
    }

    fn eval_method_call<'a, 'node>(
        &mut self,
        receiver: &Type,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        if let Type::Union(members) = receiver {
            let mut result = Type::Never;
            for member in members {
                result = result.join(&self.eval_method_call(member, name, site, environment));
            }
            return if result.is_never() { Type::Any } else { result };
        }

        if matches!(
            name,
            "nil?" | "is_a?" | "kind_of?" | "instance_of?" | "==" | "!=" | "equal?" | "eql?"
        ) {
            return Type::bool();
        }

        match receiver {
            Type::Array(element) => self.eval_array_method(element, name, site, environment),
            Type::Hash(key, value) => self.eval_hash_method(key, value, name, site, environment),
            Type::String => self.eval_string_method(name, site.argument_types),
            Type::Integer => self.eval_numeric_method(Type::Integer, name, site.argument_types),
            Type::Float => self.eval_numeric_method(Type::Float, name, site.argument_types),
            Type::True | Type::False | Type::Nil | Type::Symbol => self.eval_common_method(name),
            Type::Named(class, _) if name == "new" => Type::Named(class.clone(), Vec::new()),
            Type::Any
            | Type::Object
            | Type::Never
            | Type::Named(_, _)
            | Type::Proc(_, _)
            | Type::Intersection(_)
            | Type::Union(_)
            | Type::TypeVar(_) => {
                let _ = (site, environment);
                Type::Any
            }
        }
    }

    fn eval_array_method<'a, 'node>(
        &mut self,
        element: &Type,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "map" | "collect" => {
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(element), environment)
                });
                Type::Array(Box::new(block_type))
            }
            "each" | "each_with_index" | "select" | "filter" | "filter_map" | "reject" | "sort"
            | "reverse" | "rotate" | "shuffle" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                if name == "filter_map" {
                    Type::Array(Box::new(Type::Any))
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "first" | "last" | "at" => {
                if site.argument_types.len() > 1 {
                    Type::Array(Box::new(element.clone()))
                } else {
                    Type::union([Type::Nil, element.clone()])
                }
            }
            "[]" => {
                if site
                    .argument_types
                    .first()
                    .is_some_and(|type_| matches!(type_, Type::Integer))
                {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "compact" => Type::Array(Box::new(element.without(&Type::Nil))),
            "length" | "size" | "count" => Type::Integer,
            "empty?" | "any?" | "all?" | "none?" | "include?" => Type::bool(),
            "join" => Type::String,
            "push" | "concat" | "<<" => {
                for (argument, actual) in site.argument_nodes.iter().zip(site.argument_types) {
                    let actual = if name == "concat" {
                        self.array_element_type(actual)
                    } else {
                        actual.clone()
                    };
                    self.check_assignable(argument, &actual, element);
                }
                Type::Array(Box::new(element.clone()))
            }
            "to_a" | "to_ary" => Type::Array(Box::new(element.clone())),
            _ => Type::Any,
        }
    }

    fn eval_hash_method<'a, 'node>(
        &mut self,
        key: &Type,
        value: &Type,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "[]" | "fetch" | "default" => Type::union([Type::Nil, value.clone()]),
            "keys" => Type::Array(Box::new(key.clone())),
            "values" => Type::Array(Box::new(value.clone())),
            "each" | "each_pair" | "each_key" | "each_value" => {
                if let Some(block) = site.block {
                    let params = if name == "each_key" || name == "each_value" {
                        std::slice::from_ref(if name == "each_key" { key } else { value })
                    } else {
                        // A hash block receives the key and value. Build a
                        // temporary owned vector to keep this helper simple.
                        let expected = vec![key.clone(), value.clone()];
                        return self.eval_hash_each_block(
                            block,
                            &expected,
                            environment,
                            Type::Hash(Box::new(key.clone()), Box::new(value.clone())),
                        );
                    };
                    let _ = self.eval_block_node(block, params, environment);
                }
                Type::Hash(Box::new(key.clone()), Box::new(value.clone()))
            }
            "merge" | "dup" | "clone" => Type::Hash(Box::new(key.clone()), Box::new(value.clone())),
            "length" | "size" => Type::Integer,
            "empty?" | "include?" | "key?" | "has_key?" => Type::bool(),
            _ => Type::Any,
        }
    }

    fn eval_hash_each_block<'node>(
        &mut self,
        block: &Node<'node>,
        params: &[Type],
        environment: &mut Environment,
        result: Type,
    ) -> Type {
        let _ = self.eval_block_node(block, params, environment);
        result
    }

    fn eval_string_method(&self, name: &str, _argument_types: &[Type]) -> Type {
        match name {
            "length" | "size" | "bytesize" | "count" => Type::Integer,
            "empty?" | "start_with?" | "end_with?" | "include?" => Type::bool(),
            "to_i" | "to_int" => Type::Integer,
            "to_sym" | "intern" => Type::Symbol,
            "split" => Type::Array(Box::new(Type::String)),
            "strip" | "upcase" | "downcase" | "capitalize" | "chomp" | "to_s" | "dup" | "clone"
            | "+" => Type::String,
            _ => Type::Any,
        }
    }

    fn eval_numeric_method(&mut self, receiver: Type, name: &str, argument_types: &[Type]) -> Type {
        match name {
            "+" | "-" | "*" | "%" => {
                if receiver == Type::Float || argument_types.contains(&Type::Float) {
                    Type::Float
                } else {
                    Type::Integer
                }
            }
            "/" => {
                if receiver == Type::Integer
                    && argument_types.iter().all(|type_| *type_ == Type::Integer)
                {
                    Type::Integer
                } else {
                    Type::Float
                }
            }
            "<" | "<=" | ">" | ">=" | "between?" | "even?" | "odd?" | "zero?" => Type::bool(),
            "to_f" => Type::Float,
            "to_i" | "to_int" => Type::Integer,
            "to_s" => Type::String,
            _ => Type::Any,
        }
    }

    fn eval_common_method(&self, name: &str) -> Type {
        match name {
            "to_s" => Type::String,
            "nil?" | "to_a" => {
                if name == "to_a" {
                    Type::Array(Box::new(Type::Any))
                } else {
                    Type::bool()
                }
            }
            _ => Type::Any,
        }
    }

    fn eval_block_node<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &[Type],
        outer: &Environment,
    ) -> Type {
        let Some(block) = node.as_block_node() else {
            return Type::Any;
        };
        self.eval_block(&block, expected, outer).type_
    }

    fn eval_block<'node>(
        &mut self,
        block: &ruby_prism::BlockNode<'node>,
        expected: &[Type],
        outer: &Environment,
    ) -> Eval {
        let mut environment = outer.clone();
        if let Some(parameters) = block.parameters() {
            if let Some(parameters) = parameters
                .as_block_parameters_node()
                .and_then(|parameters| parameters.parameters())
            {
                self.bind_parameters(
                    Some(parameters),
                    Some(&MethodSig::new(expected.to_vec(), Type::Any)),
                    &mut environment,
                );
            } else if let Some(parameters) = parameters.as_parameters_node() {
                self.bind_parameters(
                    Some(parameters),
                    Some(&MethodSig::new(expected.to_vec(), Type::Any)),
                    &mut environment,
                );
            }
        }
        if let Some(body) = block.body() {
            self.eval_node(&body, &mut environment)
        } else {
            Eval::value(Type::Nil)
        }
    }

    fn invoke_signature<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        signature: &MethodSig,
        argument_nodes: &[Node<'node>],
        argument_types: &[Type],
    ) -> Type {
        if argument_types.len() < signature.required_params
            || (!signature.accepts_rest && argument_types.len() > signature.params.len())
        {
            let expected =
                if signature.required_params == signature.params.len() && !signature.accepts_rest {
                    signature.params.len().to_string()
                } else {
                    format!("at least {}", signature.required_params)
                };
            self.error(
                node,
                format!(
                    "Wrong number of arguments for `{name}`: expected {expected}, found {}",
                    argument_types.len()
                ),
            );
        }
        for ((argument, actual), expected) in argument_nodes
            .iter()
            .zip(argument_types)
            .zip(&signature.params)
        {
            self.check_assignable(argument, actual, expected);
        }
        signature.return_type.clone()
    }

    fn check_assignable<'node>(&mut self, node: &Node<'node>, actual: &Type, expected: &Type) {
        if !actual.is_subtype_of(expected) {
            self.error(node, format!("Expected `{expected}`, but found `{actual}`"));
        }
    }

    fn apply_inline_assertion<'node>(&mut self, node: &Node<'node>, actual: Type) -> Type {
        let (start, end) = prism::span(node);
        let start_line = prism::line_number(self.source, start);
        let end_line = prism::line_number(self.source, end.saturating_sub(1));
        let assertion = [start_line, end_line]
            .into_iter()
            .filter_map(|line| self.annotations.assertions.get(&line))
            .find(|assertion| {
                assertion.offset >= end
                    && self.source[end..assertion.offset]
                        .iter()
                        .all(|byte| byte.is_ascii_whitespace() || *byte == b',')
            })
            .cloned();
        let Some(assertion) = assertion else {
            return actual;
        };
        match assertion.kind {
            AssertionKind::Let => {
                self.check_assignable(node, &actual, &assertion.type_);
                assertion.type_
            }
            AssertionKind::Cast => assertion.type_,
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

    fn type_from_node<'node>(&self, node: &Node<'node>) -> Type {
        signature::parse_type(&prism::text(self.source, node))
    }

    fn constant_reference_name<'node>(&self, node: &Node<'node>) -> Option<String> {
        if let Some(constant) = node.as_constant_read_node() {
            return Some(prism::constant_name(constant.name()));
        }
        if let Some(path) = node.as_constant_path_node() {
            return Some(self.constant_path_name(&path));
        }
        None
    }

    fn constant_path_name<'node>(&self, path: &ruby_prism::ConstantPathNode<'node>) -> String {
        let name = path.name().map_or_else(String::new, prism::constant_name);
        match path.parent() {
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
        }
    }

    fn array_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => element.as_ref().clone(),
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
}
