use crate::diagnostic::Diagnostic;
use crate::prism;
use crate::signature::{self, AnnotationTable, AssertionKind, MethodSig};
use crate::types::{Type, TypeLattice};
use ruby_prism::{CallNode, DefNode, IfNode, Node, ParametersNode, UnlessNode, Visit};
use std::collections::{BTreeMap, BTreeSet};

const MAX_FIXPOINT_ROUNDS: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MethodKey {
    owner: Option<String>,
    name: String,
    singleton: bool,
}

impl MethodKey {
    fn top_level(name: impl Into<String>) -> Self {
        Self {
            owner: None,
            name: name.into(),
            singleton: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct IvarKey {
    owner: String,
    singleton: bool,
    name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ClassVarKey {
    owner: String,
    name: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ClassInfo {
    superclass: Option<String>,
    includes: Vec<String>,
    prepends: Vec<String>,
    extends: Vec<String>,
}

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment {
    locals: BTreeMap<String, Type>,
    self_type: Type,
    method_key: Option<MethodKey>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            locals: BTreeMap::new(),
            self_type: Type::Object,
            method_key: None,
        }
    }
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
        let mut result = Self {
            locals: BTreeMap::new(),
            self_type: self.self_type.clone(),
            method_key: self.method_key.clone(),
        };
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlowKind {
    Normal,
    Return,
    Raise,
    Break,
    Next,
    Retry,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Flow(u8);

impl Flow {
    const NORMAL: u8 = 1;

    fn bit(kind: FlowKind) -> u8 {
        match kind {
            FlowKind::Normal => Self::NORMAL,
            FlowKind::Return => 1 << 1,
            FlowKind::Raise => 1 << 2,
            FlowKind::Break => 1 << 3,
            FlowKind::Next => 1 << 4,
            FlowKind::Retry => 1 << 5,
        }
    }

    fn normal() -> Self {
        Self(Self::NORMAL)
    }

    fn empty() -> Self {
        Self(0)
    }

    fn abrupt(kind: FlowKind) -> Self {
        debug_assert_ne!(kind, FlowKind::Normal);
        Self(Self::bit(kind))
    }

    fn contains(self, kind: FlowKind) -> bool {
        self.0 & Self::bit(kind) != 0
    }

    fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    fn without(self, kind: FlowKind) -> Self {
        Self(self.0 & !Self::bit(kind))
    }

    fn is_terminated(self) -> bool {
        !self.contains(FlowKind::Normal)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OutcomeTypes {
    return_type: Type,
    raise_type: Type,
    break_type: Type,
    next_type: Type,
    retry_type: Type,
}

impl Default for OutcomeTypes {
    fn default() -> Self {
        Self {
            return_type: Type::Never,
            raise_type: Type::Never,
            break_type: Type::Never,
            next_type: Type::Never,
            retry_type: Type::Never,
        }
    }
}

impl OutcomeTypes {
    fn for_kind(kind: FlowKind, type_: Type) -> Self {
        let mut result = Self::default();
        result.set(kind, type_);
        result
    }

    fn set(&mut self, kind: FlowKind, type_: Type) {
        match kind {
            FlowKind::Normal => {}
            FlowKind::Return => self.return_type = type_,
            FlowKind::Raise => self.raise_type = type_,
            FlowKind::Break => self.break_type = type_,
            FlowKind::Next => self.next_type = type_,
            FlowKind::Retry => self.retry_type = type_,
        }
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            return_type: self.return_type.join(&other.return_type),
            raise_type: self.raise_type.join(&other.raise_type),
            break_type: self.break_type.join(&other.break_type),
            next_type: self.next_type.join(&other.next_type),
            retry_type: self.retry_type.join(&other.retry_type),
        }
    }

    fn without(&self, kind: FlowKind) -> Self {
        let mut result = self.clone();
        result.set(kind, Type::Never);
        result
    }

    fn all(&self) -> Type {
        Type::union([
            self.return_type.clone(),
            self.raise_type.clone(),
            self.break_type.clone(),
            self.next_type.clone(),
            self.retry_type.clone(),
        ])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Eval {
    /// The join of values produced by every possible outcome.
    type_: Type,
    /// Possible control-flow outcomes of this expression.
    flow: Flow,
    /// Value and environment continuation are present only for normal flow.
    normal_type: Option<Type>,
    /// Per-outcome values for abrupt control flow.
    abrupt: OutcomeTypes,
}

struct CallSite<'a, 'node> {
    argument_nodes: &'a [Node<'node>],
    argument_types: &'a [Type],
    block: Option<&'a Node<'node>>,
}

impl Eval {
    fn value(type_: Type) -> Self {
        Self {
            type_: type_.clone(),
            flow: Flow::normal(),
            normal_type: Some(type_),
            abrupt: OutcomeTypes::default(),
        }
    }

    fn returned(type_: Type) -> Self {
        Self::abrupt(FlowKind::Return, type_)
    }

    fn raised(type_: Type) -> Self {
        Self::abrupt(FlowKind::Raise, type_)
    }

    fn broken(type_: Type) -> Self {
        Self::abrupt(FlowKind::Break, type_)
    }

    fn continued(type_: Type) -> Self {
        Self::abrupt(FlowKind::Next, type_)
    }

    fn retried(type_: Type) -> Self {
        Self::abrupt(FlowKind::Retry, type_)
    }

    fn abrupt(kind: FlowKind, type_: Type) -> Self {
        Self {
            type_: type_.clone(),
            flow: Flow::abrupt(kind),
            normal_type: None,
            abrupt: OutcomeTypes::for_kind(kind, type_),
        }
    }

    fn from_parts(normal_type: Option<Type>, abrupt: OutcomeTypes, flow: Flow) -> Self {
        let abrupt_type = abrupt.all();
        let type_ = normal_type
            .as_ref()
            .map_or_else(|| abrupt_type.clone(), |normal| normal.join(&abrupt_type));
        Self {
            type_,
            flow,
            normal_type,
            abrupt,
        }
    }

    fn combine(left: &Self, right: &Self) -> Self {
        let normal_type = match (&left.normal_type, &right.normal_type) {
            (Some(left), Some(right)) => Some(left.join(right)),
            (Some(type_), None) | (None, Some(type_)) => Some(type_.clone()),
            (None, None) => None,
        };
        Self::from_parts(
            normal_type,
            left.abrupt.join(&right.abrupt),
            left.flow.union(right.flow),
        )
    }

    fn method_return_type(&self) -> Type {
        match (&self.normal_type, self.abrupt.return_type.is_never()) {
            (Some(normal), true) => normal.clone(),
            (Some(normal), false) => normal.join(&self.abrupt.return_type),
            (None, false) => self.abrupt.return_type.clone(),
            (None, true) => Type::Never,
        }
    }

    fn record<'src, 'node>(mut self, analyzer: &mut Analyzer<'src>, node: &Node<'node>) -> Self {
        self.type_ = analyzer.record(node, self.type_.clone());
        self
    }
}

/// The evolving summary for one user-defined method. A missing parameter or
/// return type means that no concrete evidence has reached that slot yet;
/// calls use `Never` provisionally so unresolved calls do not poison the
/// surrounding expression with `Any` before a later round can fill the slot.
#[derive(Clone, Debug, PartialEq, Eq)]
struct MethodState {
    params: Vec<Option<Type>>,
    return_type: Option<Type>,
    return_terminates: bool,
    required_params: usize,
    accepts_rest: bool,
    explicit: bool,
}

impl MethodState {
    fn explicit(signature: &MethodSig) -> Self {
        Self {
            params: signature.params.iter().cloned().map(Some).collect(),
            return_type: Some(signature.return_type.clone()),
            return_terminates: signature.return_type.is_never(),
            required_params: signature.required_params,
            accepts_rest: signature.accepts_rest,
            explicit: true,
        }
    }

    fn inferred<'node>(parameters: Option<ParametersNode<'node>>) -> Self {
        let mut params = Vec::new();
        let mut required_params = 0;

        if let Some(parameters) = parameters {
            for _ in &parameters.requireds() {
                params.push(None);
                required_params += 1;
            }
            for _ in &parameters.optionals() {
                params.push(None);
            }
            let accepts_rest = parameters.rest().is_some();
            if accepts_rest {
                params.push(None);
            }
            for _ in &parameters.posts() {
                params.push(None);
                required_params += 1;
            }
            for parameter in &parameters.keywords() {
                params.push(None);
                if parameter.as_required_keyword_parameter_node().is_some() {
                    required_params += 1;
                }
            }
            return Self {
                params,
                return_type: None,
                return_terminates: false,
                required_params,
                accepts_rest,
                explicit: false,
            };
        }

        Self {
            params,
            return_type: None,
            return_terminates: false,
            required_params,
            accepts_rest: false,
            explicit: false,
        }
    }

    fn body_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            return_type: Type::Any,
            required_params: self.required_params,
            accepts_rest: self.accepts_rest,
        }
    }

    fn call_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            return_type: self.return_type.clone().unwrap_or(Type::Never),
            required_params: self.required_params,
            accepts_rest: self.accepts_rest,
        }
    }

    fn observe_argument(&mut self, index: usize, actual: &Type) -> bool {
        if self.explicit {
            return false;
        }
        let Some(slot) = self.params.get_mut(index) else {
            return false;
        };
        let next = slot
            .as_ref()
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if slot.as_ref() == Some(&next) {
            false
        } else {
            *slot = Some(next);
            true
        }
    }

    fn set_return(&mut self, actual: &Type, terminates: bool) -> bool {
        if self.explicit {
            return false;
        }
        let next = actual.clone();
        let mut changed = false;
        if self.return_type.as_ref() != Some(&next) {
            self.return_type = Some(next);
            changed = true;
        }
        if self.return_terminates != terminates {
            self.return_terminates = terminates;
            changed = true;
        }
        changed
    }
}

struct MethodRegistrar<'a> {
    source: &'a [u8],
    methods: &'a mut BTreeMap<MethodKey, MethodState>,
    definitions: &'a mut BTreeMap<usize, MethodKey>,
    classes: &'a mut BTreeMap<String, ClassInfo>,
    aliases: &'a mut BTreeMap<MethodKey, MethodKey>,
    class_stack: Vec<String>,
    singleton_stack: Vec<String>,
    method_depth: usize,
}

impl<'pr> Visit<'pr> for MethodRegistrar<'_> {
    fn visit_def_node(&mut self, node: &DefNode<'pr>) {
        let name = prism::constant_name(node.name());
        let key = if let Some(receiver) = node.receiver() {
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
        };
        self.definitions
            .insert(prism::span(&node.as_node()).0, key.clone());
        self.methods
            .entry(key)
            .or_insert_with(|| MethodState::inferred(node.parameters()));
        self.method_depth += 1;
        ruby_prism::visit_def_node(self, node);
        self.method_depth -= 1;
    }

    fn visit_class_node(&mut self, node: &ruby_prism::ClassNode<'pr>) {
        let name = self.scope_name(&node.constant_path());
        let superclass = node.superclass().map(|superclass| {
            prism::text(self.source, &superclass)
                .trim_start_matches("::")
                .to_owned()
        });
        self.classes
            .entry(name.clone())
            .or_insert_with(|| ClassInfo {
                superclass,
                ..ClassInfo::default()
            });
        self.class_stack.push(name);
        let singleton_stack = std::mem::take(&mut self.singleton_stack);
        ruby_prism::visit_class_node(self, node);
        self.singleton_stack = singleton_stack;
        self.class_stack.pop();
    }

    fn visit_module_node(&mut self, node: &ruby_prism::ModuleNode<'pr>) {
        let name = self.scope_name(&node.constant_path());
        self.classes.entry(name.clone()).or_default();
        self.class_stack.push(name);
        let singleton_stack = std::mem::take(&mut self.singleton_stack);
        ruby_prism::visit_module_node(self, node);
        self.singleton_stack = singleton_stack;
        self.class_stack.pop();
    }

    fn visit_singleton_class_node(&mut self, node: &ruby_prism::SingletonClassNode<'pr>) {
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
            ruby_prism::visit_singleton_class_node(self, node);
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
            self.aliases.insert(
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

    fn visit_call_node(&mut self, node: &CallNode<'pr>) {
        if self.method_depth == 0 && node.receiver().is_none() && self.class_stack.last().is_some()
        {
            let name = prism::constant_name(node.name());
            let arguments = node.arguments().map(|arguments| {
                arguments
                    .arguments()
                    .into_iter()
                    .map(|argument| self.method_name(&argument))
                    .collect::<Vec<_>>()
            });
            if let Some(arguments) = arguments {
                if let Some(module) = arguments.first() {
                    let Some(owner) = self
                        .singleton_stack
                        .last()
                        .or_else(|| self.class_stack.last())
                    else {
                        ruby_prism::visit_call_node(self, node);
                        return;
                    };
                    let info = self.classes.entry(owner.clone()).or_default();
                    match name.as_str() {
                        "include" => info.includes.push(module.clone()),
                        "prepend" => info.prepends.push(module.clone()),
                        "extend" => info.extends.push(module.clone()),
                        _ => {}
                    }
                }
                if matches!(name.as_str(), "alias_method") && arguments.len() >= 2 {
                    let owner = self
                        .singleton_stack
                        .last()
                        .cloned()
                        .or_else(|| self.class_stack.last().cloned());
                    let singleton = self.singleton_stack.last().is_some();
                    self.aliases.insert(
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
            }
        }
        ruby_prism::visit_call_node(self, node);
    }
}

impl MethodRegistrar<'_> {
    fn scope_name<'node>(&self, node: &Node<'node>) -> String {
        let raw = prism::text(self.source, node);
        let raw = raw.trim_start_matches("::");
        if raw.contains("::") || self.class_stack.is_empty() {
            raw.to_owned()
        } else {
            format!(
                "{}::{raw}",
                self.class_stack.last().expect("stack is not empty")
            )
        }
    }

    fn method_name<'node>(&self, node: &Node<'node>) -> String {
        let text = prism::text(self.source, node).trim().to_owned();
        text.trim_start_matches(':')
            .trim_matches('"')
            .trim_matches('\'')
            .to_owned()
    }
}

/// Check a source buffer with direct ruby-prism parsing.
#[must_use]
pub fn check(source: &str, config: CheckerConfig) -> CheckResult {
    check_with_rbi_ranges(source, config, &[])
}

pub(crate) fn check_with_rbi_ranges(
    source: &str,
    config: CheckerConfig,
    rbi_ranges: &[(usize, usize)],
) -> CheckResult {
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
        definitions: BTreeMap::new(),
        classes: BTreeMap::new(),
        aliases: BTreeMap::new(),
        ivars: BTreeMap::new(),
        constants: BTreeMap::new(),
        class_vars: BTreeMap::new(),
        globals: BTreeMap::new(),
        report: true,
        seed_calls: false,
        rbi_ranges: rbi_ranges.to_vec(),
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
    methods: BTreeMap<MethodKey, MethodState>,
    definitions: BTreeMap<usize, MethodKey>,
    classes: BTreeMap<String, ClassInfo>,
    aliases: BTreeMap<MethodKey, MethodKey>,
    ivars: BTreeMap<IvarKey, Type>,
    constants: BTreeMap<String, Type>,
    class_vars: BTreeMap<ClassVarKey, Type>,
    globals: BTreeMap<String, Type>,
    report: bool,
    seed_calls: bool,
    rbi_ranges: Vec<(usize, usize)>,
    diagnostics: Vec<Diagnostic>,
    types: Vec<InferredType>,
}

impl<'src> Analyzer<'src> {
    fn run<'node>(mut self, root: &Node<'node>) -> CheckResult {
        self.register_methods(root);
        let parse_diagnostics = std::mem::take(&mut self.diagnostics);

        // First solve summaries without emitting diagnostics or retaining
        // transient node types. This is the same shape as Spinel's analysis:
        // all definitions are registered, then the tables are refined until
        // one complete pass makes no change.
        self.report = false;
        for _ in 0..MAX_FIXPOINT_ROUNDS {
            let previous_methods = self.methods.clone();
            let previous_ivars = self.ivars.clone();
            let previous_constants = self.constants.clone();
            let previous_class_vars = self.class_vars.clone();
            let previous_globals = self.globals.clone();
            self.ivars.clear();
            self.constants.clear();
            self.class_vars.clear();
            self.globals.clear();

            // Seed parameter slots from calls in executable scopes before
            // walking method bodies. This makes a call after its definition
            // available to that definition in the same round, just like
            // Spinel's call-site widening pass.
            self.seed_calls = true;
            self.types.clear();
            let mut environment = Environment::default();
            self.eval_node(root, &mut environment);
            self.seed_calls = false;

            self.types.clear();
            let mut environment = Environment::default();
            self.eval_node(root, &mut environment);
            if self.methods == previous_methods
                && self.ivars == previous_ivars
                && self.constants == previous_constants
                && self.class_vars == previous_class_vars
                && self.globals == previous_globals
            {
                break;
            }
        }

        // Re-run once with settled summaries. This final pass is the only pass
        // that publishes diagnostics and per-node types to callers.
        self.report = true;
        self.diagnostics = parse_diagnostics;
        self.types.clear();
        self.seed_calls = false;
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

    fn register_methods<'node>(&mut self, root: &Node<'node>) {
        self.methods = self
            .annotations
            .methods
            .iter()
            .map(|(name, signature)| {
                (
                    MethodKey::top_level(name.clone()),
                    MethodState::explicit(signature),
                )
            })
            .collect();
        let mut registrar = MethodRegistrar {
            source: self.source,
            methods: &mut self.methods,
            definitions: &mut self.definitions,
            classes: &mut self.classes,
            aliases: &mut self.aliases,
            class_stack: Vec::new(),
            singleton_stack: Vec::new(),
            method_depth: 0,
        };
        registrar.visit(root);

        // The source annotation collector intentionally stays syntax-oriented
        // and keys signatures by method name. Apply those signatures to class
        // methods too when no more specific class metadata exists.
        for (key, state) in &mut self.methods {
            if !state.explicit {
                if let Some(signature) = self.annotations.methods.get(&key.name) {
                    *state = MethodState::explicit(signature);
                }
            }
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
        if !self.report {
            return;
        }
        let (start, end) = prism::span(node);
        self.diagnostics
            .push(Diagnostic::error(self.source, message, start, end));
    }

    fn note<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.report {
            return;
        }
        let (start, end) = prism::span(node);
        self.diagnostics
            .push(Diagnostic::note(self.source, message, start, end));
    }

    fn eval_node<'node>(&mut self, node: &Node<'node>, environment: &mut Environment) -> Eval {
        if let Some(program) = node.as_program_node() {
            let result = self.eval_statements(&program.statements(), environment);
            return Eval {
                type_: self.record(node, result.type_),
                flow: result.flow,
                normal_type: result.normal_type,
                abrupt: result.abrupt,
            };
        }
        if let Some(statements) = node.as_statements_node() {
            let result = self.eval_statements(&statements, environment);
            return Eval {
                type_: self.record(node, result.type_),
                flow: result.flow,
                normal_type: result.normal_type,
                abrupt: result.abrupt,
            };
        }
        if let Some(definition) = node.as_def_node() {
            return self.eval_definition(node, &definition, environment);
        }
        if let Some(class) = node.as_class_node() {
            let class_name = self
                .constant_reference_name(&class.constant_path())
                .unwrap_or_else(|| prism::text(self.source, &class.constant_path()))
                .trim_start_matches("::")
                .to_owned();
            if let Some(body) = class.body() {
                let mut class_environment = environment.clone();
                class_environment.self_type = Type::named(class_name.clone());
                class_environment.method_key = Some(MethodKey {
                    owner: Some(class_name),
                    name: "<class-body>".to_owned(),
                    singleton: true,
                });
                self.eval_node(&body, &mut class_environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(module) = node.as_module_node() {
            let module_name = self
                .constant_reference_name(&module.constant_path())
                .unwrap_or_else(|| prism::text(self.source, &module.constant_path()))
                .trim_start_matches("::")
                .to_owned();
            if let Some(body) = module.body() {
                let mut module_environment = environment.clone();
                module_environment.self_type = Type::named(module_name.clone());
                module_environment.method_key = Some(MethodKey {
                    owner: Some(module_name),
                    name: "<module-body>".to_owned(),
                    singleton: true,
                });
                self.eval_node(&body, &mut module_environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(singleton) = node.as_singleton_class_node() {
            let expression = singleton.expression();
            let expression_type = self.eval_node(&expression, environment).type_;
            let owner = match &expression_type {
                Type::Named(owner, _) => Some(owner.clone()),
                _ => self.constant_reference_name(&expression),
            };
            if let Some(body) = singleton.body() {
                let mut singleton_environment = environment.clone();
                singleton_environment.self_type = expression_type;
                singleton_environment.method_key = Some(MethodKey {
                    owner,
                    name: "<singleton-body>".to_owned(),
                    singleton: true,
                });
                self.eval_node(&body, &mut singleton_environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(write) = node.as_constant_write_node() {
            let actual = self.eval_node(&write.value(), environment).type_;
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_constant(environment, prism::constant_name(write.name()), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_constant_path_write_node() {
            let actual = self.eval_node(&write.value(), environment).type_;
            let type_ = self.apply_inline_assertion(node, actual);
            let target = write.target();
            self.observe_constant(environment, self.constant_path_name(&target), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_class_variable_write_node() {
            let actual = self.eval_node(&write.value(), environment).type_;
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_class_var(environment, prism::constant_name(write.name()), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_class_variable_read_node() {
            let actual = self.class_var_type(environment, &prism::constant_name(read.name()));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_global_variable_write_node() {
            let actual = self.eval_node(&write.value(), environment).type_;
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_global(prism::constant_name(write.name()), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_global_variable_read_node() {
            let actual = self
                .globals
                .get(&prism::constant_name(read.name()))
                .cloned()
                .unwrap_or(Type::Any);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_instance_variable_write_node() {
            let value_node = write.value();
            let actual = self.eval_node(&value_node, environment).type_;
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_ivar(environment, prism::constant_name(write.name()), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_instance_variable_read_node() {
            let name = prism::constant_name(read.name());
            let actual = self.ivar_type(environment, &name);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
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
            let name = prism::constant_name(constant.name());
            let actual = self.constant_type(environment, &name);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(path) = node.as_constant_path_node() {
            let actual = self.constant_type(environment, &self.constant_path_name(&path));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if node.as_self_node().is_some() {
            let type_ = self.apply_inline_assertion(node, environment.self_type.clone());
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
        if let Some(lambda) = node.as_lambda_node() {
            let signature = MethodState::inferred(
                lambda
                    .parameters()
                    .and_then(|parameters| parameters.as_parameters_node()),
            )
            .body_signature();
            let parameters = lambda
                .parameters()
                .and_then(|parameters| parameters.as_parameters_node());
            let mut closure_environment = environment.clone();
            self.bind_parameters(parameters, Some(&signature), &mut closure_environment);
            let body_result = lambda
                .body()
                .map(|body| self.eval_node(&body, &mut closure_environment))
                .unwrap_or_else(|| Eval::value(Type::Nil));
            let return_type = body_result.method_return_type();
            let type_ = self
                .apply_inline_assertion(node, Type::Proc(signature.params, Box::new(return_type)));
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
                    ..result
                };
            }
            let type_ = self.apply_inline_assertion(node, Type::Nil);
            return Eval::value(self.record(node, type_));
        }
        if let Some(begin) = node.as_begin_node() {
            return self.eval_begin(node, &begin, environment);
        }
        if let Some(rescue) = node.as_rescue_modifier_node() {
            return self.eval_rescue_modifier(node, &rescue, environment);
        }
        if let Some(if_node) = node.as_if_node() {
            return self.eval_if(node, &if_node, environment);
        }
        if let Some(unless) = node.as_unless_node() {
            return self.eval_unless(node, &unless, environment);
        }
        if let Some(case_node) = node.as_case_node() {
            return self.eval_case(node, &case_node, environment);
        }
        if let Some(case_match) = node.as_case_match_node() {
            return self.eval_case_match(node, &case_match, environment);
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
            let type_ = self.eval_control_arguments(return_node.arguments(), environment);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::returned(self.record(node, type_));
        }
        if let Some(break_node) = node.as_break_node() {
            let type_ = self.eval_control_arguments(break_node.arguments(), environment);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::broken(self.record(node, type_));
        }
        if let Some(next_node) = node.as_next_node() {
            let type_ = self.eval_control_arguments(next_node.arguments(), environment);
            let type_ = self.apply_inline_assertion(node, type_);
            return Eval::continued(self.record(node, type_));
        }
        if node.as_retry_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Never);
            return Eval::retried(self.record(node, type_));
        }
        if let Some(super_node) = node.as_super_node() {
            let actual = self.eval_super(node, super_node.arguments(), None, environment);
            let type_ = self.apply_inline_assertion(node, actual);
            let type_ = self.record(node, type_);
            if self.super_terminates(environment) {
                return Eval::raised(type_);
            } else {
                return Eval::value(type_);
            }
        }
        if let Some(super_node) = node.as_forwarding_super_node() {
            let actual = self.eval_super(node, None, Some(&super_node), environment);
            let type_ = self.apply_inline_assertion(node, actual);
            let type_ = self.record(node, type_);
            if self.super_terminates(environment) {
                return Eval::raised(type_);
            } else {
                return Eval::value(type_);
            }
        }
        if let Some(call) = node.as_call_node() {
            let mut result = self.eval_call(node, &call, environment);
            let type_ = self.apply_inline_assertion(node, result.type_.clone());
            if result.normal_type.is_some() {
                result.normal_type = Some(type_.clone());
            }
            result.type_ = self.record(node, type_);
            return result;
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
            let statements = while_node.statements();
            let mut result = self.eval_loop(&predicate, statements.as_ref(), environment, true);
            let type_ = self.apply_inline_assertion(node, result.type_.clone());
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(until_node) = node.as_until_node() {
            let predicate = until_node.predicate();
            let statements = until_node.statements();
            let mut result = self.eval_loop(&predicate, statements.as_ref(), environment, false);
            let type_ = self.apply_inline_assertion(node, result.type_.clone());
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(for_node) = node.as_for_node() {
            return self.eval_for(node, &for_node, environment);
        }

        let type_ = self.apply_inline_assertion(node, Type::Any);
        Eval::value(self.record(node, type_))
    }

    fn eval_begin<'node>(
        &mut self,
        node: &Node<'node>,
        begin: &ruby_prism::BeginNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let entry = environment.clone();
        let mut normal_environment = entry.clone();
        let body_result = if let Some(statements) = begin.statements() {
            self.eval_statements(&statements, &mut normal_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let mut result = body_result;

        // `else` runs only on the normal path. Return/raise/break/etc. from
        // the body bypass it and remain visible to the enclosing construct.
        if let Some(else_clause) = begin.else_clause() {
            if result.flow.contains(FlowKind::Normal) {
                let else_result = if let Some(statements) = else_clause.statements() {
                    self.eval_statements(&statements, &mut normal_environment)
                } else {
                    Eval::value(Type::Nil)
                };
                result = Eval::from_parts(
                    else_result.normal_type.clone(),
                    result.abrupt.join(&else_result.abrupt),
                    result
                        .flow
                        .without(FlowKind::Normal)
                        .union(else_result.flow),
                );
            }
        }

        let mut merged_environment = normal_environment;
        if let Some(rescue) = begin.rescue_clause() {
            let body_flow = result.flow;
            let (rescue_result, rescue_environment) = self.eval_rescue_chain(rescue, &entry);
            let retrying = rescue_result.flow.contains(FlowKind::Retry);
            let mut rescue_flow = rescue_result.flow.without(FlowKind::Retry);
            let mut rescue_normal_type = rescue_result.normal_type.clone();
            let mut rescue_environment = rescue_environment;
            let rescue_abrupt = rescue_result.abrupt.without(FlowKind::Retry);
            if retrying {
                // `retry` re-enters the begin body. We do not execute a
                // second syntax tree traversal here; model the re-entry as a
                // conservative normal path so statements after the begin
                // remain reachable and the surrounding lattice stays sound.
                rescue_flow = rescue_flow.union(Flow::normal());
                rescue_normal_type = Some(
                    rescue_normal_type
                        .unwrap_or_else(|| result.normal_type.clone().unwrap_or(Type::Any)),
                );
                rescue_environment = rescue_environment.join(&entry);
            }
            result = Eval::from_parts(
                match (&result.normal_type, &rescue_normal_type) {
                    (Some(left), Some(right)) => Some(left.join(right)),
                    (Some(type_), None) | (None, Some(type_)) => Some(type_.clone()),
                    (None, None) => None,
                },
                result.abrupt.without(FlowKind::Raise).join(&rescue_abrupt),
                body_flow.without(FlowKind::Raise).union(rescue_flow),
            );
            merged_environment = self.join_flow_environments(
                &merged_environment,
                body_flow,
                &rescue_environment,
                rescue_flow,
            );
        }
        *environment = merged_environment;

        if let Some(ensure) = begin.ensure_clause() {
            if let Some(statements) = ensure.statements() {
                let prior = result;
                let ensure_result = self.eval_statements(&statements, environment);
                if ensure_result.flow.is_terminated() {
                    result = ensure_result;
                } else {
                    result = Eval::from_parts(
                        prior.normal_type.clone(),
                        prior.abrupt.join(&ensure_result.abrupt),
                        prior
                            .flow
                            .union(ensure_result.flow.without(FlowKind::Normal)),
                    );
                }
            }
        }

        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn eval_rescue_modifier<'node>(
        &mut self,
        node: &Node<'node>,
        rescue: &ruby_prism::RescueModifierNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let entry = environment.clone();
        let mut primary_environment = entry.clone();
        let primary = self.eval_node(&rescue.expression(), &mut primary_environment);
        let mut rescue_environment = entry;
        let fallback = self.eval_node(&rescue.rescue_expression(), &mut rescue_environment);
        *environment = self.join_flow_environments(
            &primary_environment,
            primary.flow,
            &rescue_environment,
            fallback.flow,
        );
        let mut result = Eval::from_parts(
            match (&primary.normal_type, &fallback.normal_type) {
                (Some(left), Some(right)) => Some(left.join(right)),
                (Some(type_), None) | (None, Some(type_)) => Some(type_.clone()),
                (None, None) => None,
            },
            primary
                .abrupt
                .without(FlowKind::Raise)
                .join(&fallback.abrupt),
            primary.flow.without(FlowKind::Raise).union(fallback.flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn eval_rescue_chain<'node>(
        &mut self,
        first: ruby_prism::RescueNode<'node>,
        base: &Environment,
    ) -> (Eval, Environment) {
        let mut next = Some(first);
        let mut result: Option<Eval> = None;
        let mut result_environment: Option<Environment> = None;
        while let Some(rescue) = next {
            let mut rescue_environment = base.clone();
            let mut exception_type = Type::Never;
            for exception in &rescue.exceptions() {
                exception_type =
                    exception_type.join(&self.eval_node(&exception, &mut rescue_environment).type_);
            }
            if exception_type.is_never() {
                exception_type = Type::named("StandardError");
            }
            if let Some(reference) = rescue.reference() {
                self.bind_for_target(&reference, exception_type, &mut rescue_environment);
            }
            let rescue_result = if let Some(statements) = rescue.statements() {
                self.eval_statements(&statements, &mut rescue_environment)
            } else {
                Eval::value(Type::Nil)
            };
            result = Some(match result {
                Some(current) => Eval::combine(&current, &rescue_result),
                None => rescue_result,
            });
            result_environment = Some(match result_environment {
                Some(current) => current.join(&rescue_environment),
                None => rescue_environment,
            });
            next = rescue.subsequent();
        }
        (
            result.unwrap_or_else(|| Eval::value(Type::Nil)),
            result_environment.unwrap_or_else(|| base.clone()),
        )
    }

    fn eval_case<'node>(
        &mut self,
        node: &Node<'node>,
        case_node: &ruby_prism::CaseNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = case_node.predicate();
        if let Some(predicate) = predicate.as_ref() {
            self.eval_node(predicate, environment);
        }
        let base = environment.clone();
        let mut branch_environment: Option<Environment> = None;
        let mut result: Option<Eval> = None;

        for condition in &case_node.conditions() {
            let Some(when_node) = condition.as_when_node() else {
                continue;
            };
            let mut when_environment = base.clone();
            let mut condition_type = Type::Never;
            for value in &when_node.conditions() {
                let value_type = self.eval_node(&value, &mut when_environment).type_;
                condition_type = condition_type.join(&value_type);
            }
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target(predicate, &mut when_environment, &condition_type);
            }
            let when_result = if let Some(statements) = when_node.statements() {
                self.eval_statements(&statements, &mut when_environment)
            } else {
                Eval::value(Type::Nil)
            };
            let previous_flow = result
                .as_ref()
                .map_or_else(Flow::empty, |result| result.flow);
            let when_flow = when_result.flow;
            result = Some(match result {
                Some(current) => Eval::combine(&current, &when_result),
                None => when_result,
            });
            branch_environment = Some(match branch_environment {
                Some(current) => self.join_flow_environments(
                    &current,
                    previous_flow,
                    &when_environment,
                    when_flow,
                ),
                None => when_environment,
            });
        }

        let mut else_environment = base.clone();
        let else_result = if let Some(else_clause) = case_node.else_clause() {
            if let Some(statements) = else_clause.statements() {
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            // Without an else clause, the case may take no branch and yields
            // nil while preserving the incoming environment.
            Eval::value(Type::Nil)
        };
        let previous_flow = result
            .as_ref()
            .map_or_else(Flow::empty, |result| result.flow);
        let else_flow = else_result.flow;
        result = Some(match result {
            Some(current) => Eval::combine(&current, &else_result),
            None => else_result,
        });
        branch_environment = Some(match branch_environment {
            Some(current) => {
                self.join_flow_environments(&current, previous_flow, &else_environment, else_flow)
            }
            None => else_environment,
        });
        *environment = branch_environment.expect("case always has an implicit else path");
        let mut result = result.expect("case always has an implicit else path");
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn narrow_case_target<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        condition_type: &Type,
    ) {
        if let Some(local) = predicate.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            let current = environment.get(&name);
            environment.bind(name, current.meet(condition_type));
        }
    }

    fn eval_case_match<'node>(
        &mut self,
        node: &Node<'node>,
        case_node: &ruby_prism::CaseMatchNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let predicate = case_node.predicate();
        if let Some(predicate) = predicate.as_ref() {
            self.eval_node(predicate, environment);
        }
        let base = environment.clone();
        let candidate = predicate
            .as_ref()
            .map_or(Type::Any, |predicate| self.node_type(predicate, &base));
        let mut branch_environment: Option<Environment> = None;
        let mut result: Option<Eval> = None;

        for condition in &case_node.conditions() {
            let Some(in_node) = condition.as_in_node() else {
                continue;
            };
            let mut in_environment = base.clone();
            let constraint = self.bind_pattern(&in_node.pattern(), &candidate, &mut in_environment);
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target(predicate, &mut in_environment, &constraint);
            }
            let in_result = if let Some(statements) = in_node.statements() {
                self.eval_statements(&statements, &mut in_environment)
            } else {
                Eval::value(Type::Nil)
            };
            let previous_flow = result
                .as_ref()
                .map_or_else(Flow::empty, |result| result.flow);
            let in_flow = in_result.flow;
            result = Some(match result {
                Some(current) => Eval::combine(&current, &in_result),
                None => in_result,
            });
            branch_environment = Some(match branch_environment {
                Some(current) => {
                    self.join_flow_environments(&current, previous_flow, &in_environment, in_flow)
                }
                None => in_environment,
            });
        }

        let mut else_environment = base;
        let else_result = if let Some(else_clause) = case_node.else_clause() {
            if let Some(statements) = else_clause.statements() {
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            Eval::value(Type::Nil)
        };
        let previous_flow = result
            .as_ref()
            .map_or_else(Flow::empty, |result| result.flow);
        let else_flow = else_result.flow;
        result = Some(match result {
            Some(current) => Eval::combine(&current, &else_result),
            None => else_result,
        });
        branch_environment = Some(match branch_environment {
            Some(current) => {
                self.join_flow_environments(&current, previous_flow, &else_environment, else_flow)
            }
            None => else_environment,
        });
        *environment = branch_environment.expect("pattern match always has an else path");
        let mut result = result.expect("pattern match always has an else path");
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn node_type<'node>(&mut self, node: &Node<'node>, environment: &Environment) -> Type {
        let mut environment = environment.clone();
        self.eval_node(node, &mut environment).type_
    }

    fn bind_pattern<'node>(
        &mut self,
        pattern: &Node<'node>,
        candidate: &Type,
        environment: &mut Environment,
    ) -> Type {
        if let Some(capture) = pattern.as_capture_pattern_node() {
            let constraint = self.pattern_constraint(&capture.value(), candidate, environment);
            let narrowed = if constraint.is_any() {
                candidate.clone()
            } else {
                candidate.meet(&constraint)
            };
            environment.bind(
                prism::constant_name(capture.target().name()),
                narrowed.clone(),
            );
            return if narrowed.is_never() {
                constraint
            } else {
                narrowed
            };
        }
        if let Some(target) = pattern.as_local_variable_target_node() {
            environment.bind(prism::constant_name(target.name()), candidate.clone());
            return Type::Any;
        }
        if let Some(array) = pattern.as_array_pattern_node() {
            let element = self.array_element_type(candidate);
            let mut constraint = Type::Never;
            for child in &array.requireds() {
                constraint = constraint.join(&self.bind_pattern(&child, &element, environment));
            }
            if let Some(rest) = array.rest() {
                let rest_type = Type::Array(Box::new(element.clone()));
                constraint = constraint.join(&self.bind_pattern(&rest, &rest_type, environment));
            }
            for child in &array.posts() {
                constraint = constraint.join(&self.bind_pattern(&child, &element, environment));
            }
            let element_constraint = if constraint.is_never() {
                Type::Any
            } else {
                constraint
            };
            return Type::Array(Box::new(element_constraint));
        }
        if let Some(hash) = pattern.as_hash_pattern_node() {
            let value = match candidate {
                Type::Hash(_, value) => value.as_ref().clone(),
                _ => Type::Any,
            };
            let mut value_constraint = Type::Never;
            for child in &hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    value_constraint = value_constraint.join(&self.bind_pattern(
                        &assoc.value(),
                        &value,
                        environment,
                    ));
                }
            }
            let value_constraint = if value_constraint.is_never() {
                Type::Any
            } else {
                value_constraint
            };
            return Type::Hash(Box::new(Type::Any), Box::new(value_constraint));
        }
        if let Some(alternation) = pattern.as_alternation_pattern_node() {
            let left = self.pattern_constraint(&alternation.left(), candidate, environment);
            let right = self.pattern_constraint(&alternation.right(), candidate, environment);
            return left.join(&right);
        }
        self.pattern_constraint(pattern, candidate, environment)
    }

    fn pattern_constraint<'node>(
        &mut self,
        pattern: &Node<'node>,
        candidate: &Type,
        environment: &mut Environment,
    ) -> Type {
        if pattern.as_local_variable_target_node().is_some()
            || pattern.as_implicit_node().is_some()
            || pattern.as_implicit_rest_node().is_some()
        {
            return Type::Any;
        }
        if let Some(capture) = pattern.as_capture_pattern_node() {
            return self.pattern_constraint(&capture.value(), candidate, environment);
        }
        if let Some(array) = pattern.as_array_pattern_node() {
            let element = self.array_element_type(candidate);
            let mut element_constraint = Type::Never;
            for child in &array.requireds() {
                element_constraint = element_constraint.join(&self.pattern_constraint(
                    &child,
                    &element,
                    environment,
                ));
            }
            for child in &array.posts() {
                element_constraint = element_constraint.join(&self.pattern_constraint(
                    &child,
                    &element,
                    environment,
                ));
            }
            return Type::Array(Box::new(if element_constraint.is_never() {
                Type::Any
            } else {
                element_constraint
            }));
        }
        if let Some(alternation) = pattern.as_alternation_pattern_node() {
            return self
                .pattern_constraint(&alternation.left(), candidate, environment)
                .join(&self.pattern_constraint(&alternation.right(), candidate, environment));
        }
        self.node_type(pattern, environment)
    }

    fn eval_control_arguments<'node>(
        &mut self,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        environment: &mut Environment,
    ) -> Type {
        let Some(arguments) = arguments else {
            return Type::Nil;
        };
        let mut result = Type::Nil;
        for argument in &arguments.arguments() {
            result = self.eval_node(&argument, environment).type_;
        }
        result
    }

    fn eval_loop<'node>(
        &mut self,
        predicate: &Node<'node>,
        statements: Option<&ruby_prism::StatementsNode<'node>>,
        environment: &mut Environment,
        predicate_truthy: bool,
    ) -> Eval {
        let entry = environment.clone();
        let mut head = entry.clone();
        let mut exit_environment: Option<Environment> = None;
        let mut break_type = Type::Never;
        let mut abrupt = OutcomeTypes::default();
        let mut terminal_flow = Flow::empty();
        for _ in 0..MAX_FIXPOINT_ROUNDS {
            let mut condition_environment = head.clone();
            let condition_result = self.eval_node(predicate, &mut condition_environment);
            abrupt = abrupt.join(
                &condition_result
                    .abrupt
                    .without(FlowKind::Break)
                    .without(FlowKind::Next),
            );
            terminal_flow = terminal_flow.union(
                condition_result
                    .flow
                    .without(FlowKind::Normal)
                    .without(FlowKind::Break)
                    .without(FlowKind::Next),
            );
            if !condition_result.flow.contains(FlowKind::Normal) {
                break;
            }
            exit_environment = Some(match exit_environment {
                Some(current) => current.join(&condition_environment),
                None => condition_environment.clone(),
            });
            let mut body_environment = condition_environment;
            self.narrow_from_predicate(predicate, &mut body_environment, predicate_truthy);
            let body_result = statements.map_or_else(
                || Eval::value(Type::Nil),
                |statements| self.eval_statements(statements, &mut body_environment),
            );
            let body_terminal_flow = body_result
                .flow
                .without(FlowKind::Normal)
                .without(FlowKind::Break)
                .without(FlowKind::Next);
            terminal_flow = terminal_flow.union(body_terminal_flow);
            if body_terminal_flow.0 != 0 {
                abrupt = abrupt.join(
                    &body_result
                        .abrupt
                        .without(FlowKind::Break)
                        .without(FlowKind::Next),
                );
            }
            if body_result.flow.contains(FlowKind::Break) {
                break_type = break_type.join(&body_result.abrupt.break_type);
                exit_environment = Some(match exit_environment {
                    Some(current) => current.join(&body_environment),
                    None => body_environment.clone(),
                });
            }
            if !body_result.flow.contains(FlowKind::Normal)
                && !body_result.flow.contains(FlowKind::Next)
            {
                break;
            }
            let next = head.join(&body_environment);
            if next == head {
                break;
            }
            head = next;
        }
        let mut result_environment = entry.join(&head);
        if let Some(exit_environment) = exit_environment {
            result_environment = result_environment.join(&exit_environment);
        }
        *environment = result_environment;
        let normal_type = Type::union([Type::Nil, break_type]);
        Eval::from_parts(
            Some(normal_type),
            abrupt,
            Flow::normal().union(terminal_flow),
        )
    }

    fn eval_for<'node>(
        &mut self,
        node: &Node<'node>,
        for_node: &ruby_prism::ForNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let collection = for_node.collection();
        let collection_result = self.eval_node(&collection, environment);
        if !collection_result.flow.contains(FlowKind::Normal) {
            return collection_result.record(self, node);
        }
        let collection_type = collection_result.type_;
        let element_type = self.array_element_type(&collection_type);
        let entry = environment.clone();
        let mut head = entry.clone();
        let mut exit_environment: Option<Environment> = None;
        let mut break_type = Type::Never;
        let mut abrupt = collection_result
            .abrupt
            .without(FlowKind::Break)
            .without(FlowKind::Next);
        let mut terminal_flow = collection_result
            .flow
            .without(FlowKind::Normal)
            .without(FlowKind::Break)
            .without(FlowKind::Next);
        for _ in 0..MAX_FIXPOINT_ROUNDS {
            let mut body_environment = head.clone();
            self.bind_for_target(
                &for_node.index(),
                element_type.clone(),
                &mut body_environment,
            );
            let body_result = for_node.statements().map_or_else(
                || Eval::value(Type::Nil),
                |statements| self.eval_statements(&statements, &mut body_environment),
            );
            let body_terminal_flow = body_result
                .flow
                .without(FlowKind::Normal)
                .without(FlowKind::Break)
                .without(FlowKind::Next);
            terminal_flow = terminal_flow.union(body_terminal_flow);
            if body_terminal_flow.0 != 0 {
                abrupt = abrupt.join(
                    &body_result
                        .abrupt
                        .without(FlowKind::Break)
                        .without(FlowKind::Next),
                );
            }
            if body_result.flow.contains(FlowKind::Break) {
                break_type = break_type.join(&body_result.abrupt.break_type);
                exit_environment = Some(match exit_environment {
                    Some(current) => current.join(&body_environment),
                    None => body_environment.clone(),
                });
            }
            if !body_result.flow.contains(FlowKind::Normal)
                && !body_result.flow.contains(FlowKind::Next)
            {
                break;
            }
            let next = head.join(&body_environment);
            if next == head {
                break;
            }
            head = next;
        }
        let mut result_environment = entry.join(&head);
        if let Some(exit_environment) = exit_environment {
            result_environment = result_environment.join(&exit_environment);
        }
        *environment = result_environment;
        let normal_type = Type::union([Type::Nil, break_type]);
        let mut result = Eval::from_parts(
            Some(normal_type),
            abrupt,
            Flow::normal().union(terminal_flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn bind_for_target<'node>(
        &self,
        target: &Node<'node>,
        type_: Type,
        environment: &mut Environment,
    ) {
        if let Some(write) = target.as_local_variable_write_node() {
            environment.bind(prism::constant_name(write.name()), type_);
            return;
        }
        if let Some(target) = target.as_local_variable_target_node() {
            environment.bind(prism::constant_name(target.name()), type_);
            return;
        }
        if let Some(multi) = target.as_multi_target_node() {
            for child in &multi.lefts() {
                self.bind_for_target(&child, type_.clone(), environment);
            }
            if let Some(rest) = multi.rest() {
                self.bind_for_target(&rest, Type::Array(Box::new(type_.clone())), environment);
            }
            for child in &multi.rights() {
                self.bind_for_target(&child, type_.clone(), environment);
            }
        }
    }

    fn eval_statements<'node>(
        &mut self,
        statements: &ruby_prism::StatementsNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let mut flow = Flow::normal();
        let mut normal_type = Some(Type::Nil);
        let mut abrupt = OutcomeTypes::default();
        let body = statements.body();
        for child in &body {
            let result = self.eval_node(&child, environment);
            abrupt = abrupt.join(&result.abrupt);
            flow = flow.without(FlowKind::Normal).union(result.flow);
            normal_type = result.normal_type;
            if result.flow.is_terminated() {
                normal_type = None;
                break;
            }
        }
        Eval::from_parts(normal_type, abrupt, flow)
    }

    fn eval_definition<'node>(
        &mut self,
        node: &Node<'node>,
        definition: &DefNode<'node>,
        outer: &mut Environment,
    ) -> Eval {
        let name = prism::constant_name(definition.name());
        let key = self
            .definitions
            .get(&prism::span(node).0)
            .cloned()
            .unwrap_or_else(|| MethodKey::top_level(name.clone()));
        let state = self
            .methods
            .get(&key)
            .cloned()
            .unwrap_or_else(|| MethodState::inferred(definition.parameters()));
        if self.seed_calls {
            return Eval::value(self.record(node, Type::Nil));
        }
        let body_signature = state.body_signature();
        let mut method_environment = Environment {
            self_type: key
                .owner
                .as_ref()
                .map_or(Type::Object, |owner| Type::named(owner.clone())),
            method_key: Some(key.clone()),
            ..Environment::default()
        };
        self.bind_parameters(
            definition.parameters(),
            Some(&body_signature),
            &mut method_environment,
        );

        let body_result = if let Some(body) = definition.body() {
            self.eval_node(&body, &mut method_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let inferred_return = body_result.method_return_type();
        if state.explicit && !self.is_rbi_definition(node) {
            let expected = state.call_signature();
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
        } else if let Some(current) = self.methods.get_mut(&key) {
            current.set_return(
                &inferred_return,
                body_result.flow == Flow::abrupt(FlowKind::Raise),
            );
        } else {
            let mut current = MethodState::inferred(definition.parameters());
            current.set_return(
                &inferred_return,
                body_result.flow == Flow::abrupt(FlowKind::Raise),
            );
            self.methods.insert(key, current);
        }
        let _ = outer;
        Eval::value(self.record(node, Type::Nil))
    }

    fn is_rbi_definition(&self, node: &Node<'_>) -> bool {
        let (start, end) = prism::span(node);
        self.rbi_ranges
            .iter()
            .any(|(range_start, range_end)| start >= *range_start && end <= *range_end)
    }

    fn eval_super<'node>(
        &mut self,
        node: &Node<'node>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        forwarding: Option<&ruby_prism::ForwardingSuperNode<'node>>,
        environment: &mut Environment,
    ) -> Type {
        let Some(current) = environment.method_key.clone() else {
            return Type::Any;
        };
        let target = self.super_method_key(&current);
        let mut argument_nodes = Vec::new();
        let argument_types = if let Some(forwarding) = forwarding {
            if let Some(block) = forwarding.block() {
                let _ = self.eval_block(&block, &[], environment);
            }
            self.methods
                .get(&current)
                .map(|state| state.call_signature().params)
                .unwrap_or_default()
        } else {
            argument_nodes = arguments
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            argument_nodes
                .iter()
                .map(|argument| self.eval_node(argument, environment).type_)
                .collect::<Vec<_>>()
        };
        let Some(target) = target else {
            return Type::Any;
        };
        let Some(signature) = self.observe_call(&target, &argument_types) else {
            return Type::Any;
        };
        self.invoke_signature(
            node,
            &target.name,
            &signature,
            &argument_nodes,
            &argument_types,
        )
    }

    fn super_method_key(&self, current: &MethodKey) -> Option<MethodKey> {
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
            if self.methods.contains_key(&candidate) {
                return Some(candidate);
            }
            if self.aliases.contains_key(&candidate) {
                if let Some(resolved) = self.resolve_method_key_inner(&candidate, &mut visited) {
                    return Some(resolved);
                }
            }
        }
        None
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

        *environment = self.join_flow_environments(
            &then_environment,
            then_result.flow,
            &else_environment,
            else_result.flow,
        );
        let mut result = Eval::combine(&then_result, &else_result);
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
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

        *environment = self.join_flow_environments(
            &then_environment,
            then_result.flow,
            &else_environment,
            else_result.flow,
        );
        let mut result = Eval::combine(&then_result, &else_result);
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
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

    fn join_flow_environments(
        &self,
        left: &Environment,
        left_flow: Flow,
        right: &Environment,
        right_flow: Flow,
    ) -> Environment {
        match (
            left_flow.contains(FlowKind::Normal),
            right_flow.contains(FlowKind::Normal),
        ) {
            (true, false) => left.clone(),
            (false, true) => right.clone(),
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
    ) -> Eval {
        let name = prism::constant_name(call.name());
        let argument_nodes = call
            .arguments()
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        let mut argument_types = Vec::with_capacity(argument_nodes.len());
        let mut abrupt = OutcomeTypes::default();
        let mut abrupt_flow = Flow::empty();
        let mut all_normal = true;
        let receiver_node = call.receiver();
        let receiver_type = if let Some(receiver) = receiver_node.as_ref() {
            let result = self.eval_node(receiver, environment);
            abrupt = abrupt.join(&result.abrupt);
            abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
            all_normal &= result.flow.contains(FlowKind::Normal);
            result.type_
        } else {
            Type::Object
        };
        for argument in &argument_nodes {
            let result = self.eval_node(argument, environment);
            argument_types.push(result.type_.clone());
            abrupt = abrupt.join(&result.abrupt);
            abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
            all_normal &= result.flow.contains(FlowKind::Normal);
        }

        let callee_type = if receiver_node
            .as_ref()
            .is_some_and(|receiver| self.constant_reference_name(receiver).as_deref() == Some("T"))
        {
            self.eval_t_call(node, &name, &argument_nodes, &argument_types, environment)
        } else if receiver_node.is_none()
            && matches!(name.as_str(), "lambda" | "proc")
            && call.block().is_some()
        {
            let return_type = call.block().as_ref().map_or(Type::Any, |block| {
                self.eval_block_node(block, &[], environment)
            });
            Type::Proc(Vec::new(), Box::new(return_type))
        } else if receiver_node.is_none() {
            let key = self.implicit_method_key(&name, environment);
            if let Some(signature) = self.observe_call(&key, &argument_types) {
                self.invoke_signature(node, &name, &signature, &argument_nodes, &argument_types)
            } else if key.singleton {
                if let Some(owner) = key.owner.clone() {
                    if name == "new" {
                        self.infer_initializer_call(node, &owner, &argument_nodes, &argument_types);
                        Type::named(owner)
                    } else {
                        self.eval_global_call(
                            node,
                            &name,
                            &argument_nodes,
                            &argument_types,
                            environment,
                        )
                    }
                } else {
                    self.eval_global_call(
                        node,
                        &name,
                        &argument_nodes,
                        &argument_types,
                        environment,
                    )
                }
            } else {
                self.eval_global_call(node, &name, &argument_nodes, &argument_types, environment)
            }
        } else {
            let block = call.block();
            let site = CallSite {
                argument_nodes: &argument_nodes,
                argument_types: &argument_types,
                block: block.as_ref(),
            };
            let mut result = if let Some(key) =
                self.receiver_method_key(receiver_node.as_ref(), &receiver_type, &name, environment)
            {
                if let Some(signature) = self.observe_call(&key, &argument_types) {
                    self.invoke_signature(node, &name, &signature, &argument_nodes, &argument_types)
                } else {
                    self.eval_method_call(&receiver_type, &name, &site, environment)
                }
            } else {
                self.eval_method_call(&receiver_type, &name, &site, environment)
            };
            if name == "new"
                && receiver_node
                    .as_ref()
                    .is_some_and(|receiver| self.constant_reference_name(receiver).is_some())
            {
                if let Type::Named(owner, _) = &receiver_type {
                    self.infer_initializer_call(node, owner, &argument_nodes, &argument_types);
                    result = Type::named(owner.clone());
                }
            }
            if call.is_safe_navigation() && !receiver_type.is_any() {
                Type::union([Type::Nil, result])
            } else {
                result
            }
        };

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

    fn call_terminates<'node>(
        &self,
        call: &CallNode<'node>,
        environment: &Environment,
        receiver_type: &Type,
        type_: &Type,
    ) -> bool {
        let name = prism::constant_name(call.name());
        if call.receiver().is_none() && matches!(name.as_str(), "raise" | "fail" | "abort") {
            return true;
        }
        if call
            .receiver()
            .as_ref()
            .is_some_and(|receiver| self.constant_reference_name(receiver).as_deref() == Some("T"))
        {
            return matches!(name.as_str(), "noreturn" | "absurd");
        }
        if !type_.is_never() {
            return false;
        }
        let key = if let Some(receiver) = call.receiver() {
            let Some(key) =
                self.receiver_method_key(Some(&receiver), receiver_type, &name, environment)
            else {
                return false;
            };
            key
        } else {
            self.implicit_method_key(&name, environment)
        };
        let Some(key) = self.resolve_method_key(&key) else {
            return false;
        };
        self.methods.get(&key).is_some_and(|state| {
            state.return_terminates && state.return_type.as_ref().is_some_and(Type::is_never)
        })
    }

    fn super_terminates(&self, environment: &Environment) -> bool {
        let Some(current) = environment.method_key.as_ref() else {
            return false;
        };
        let Some(target) = self.super_method_key(current) else {
            return false;
        };
        self.methods.get(&target).is_some_and(|state| {
            state.return_terminates && state.return_type.as_ref().is_some_and(Type::is_never)
        })
    }

    fn observe_call(&mut self, key: &MethodKey, argument_types: &[Type]) -> Option<MethodSig> {
        let key = self.resolve_method_key(key)?;
        let state = self.methods.get_mut(&key)?;
        for (index, actual) in argument_types.iter().enumerate() {
            state.observe_argument(index, actual);
        }
        Some(state.call_signature())
    }

    fn resolve_method_key(&self, key: &MethodKey) -> Option<MethodKey> {
        self.resolve_method_key_inner(key, &mut BTreeSet::new())
    }

    fn resolve_method_key_inner(
        &self,
        key: &MethodKey,
        visited: &mut BTreeSet<MethodKey>,
    ) -> Option<MethodKey> {
        if !visited.insert(key.clone()) {
            return None;
        }
        let mut candidates = Vec::new();
        if let Some(owner) = &key.owner {
            self.append_method_candidates(
                owner,
                &key.name,
                key.singleton,
                &mut BTreeSet::new(),
                &mut candidates,
            );
        } else {
            candidates.push(key.clone());
        }
        for candidate in candidates {
            if self.methods.contains_key(&candidate) {
                return Some(candidate);
            }
            if let Some(target) = self.aliases.get(&candidate) {
                if let Some(resolved) = self.resolve_method_key_inner(target, visited) {
                    return Some(resolved);
                }
            }
        }
        None
    }

    fn append_method_candidates(
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
        let info = self.classes.get(owner);
        if let Some(info) = info {
            if singleton {
                for module in info.extends.iter().rev() {
                    self.append_method_candidates(module, name, false, visited, candidates);
                }
            } else {
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
            if !singleton {
                for module in info.includes.iter().rev() {
                    self.append_method_candidates(module, name, false, visited, candidates);
                }
            }
            if let Some(superclass) = &info.superclass {
                self.append_method_candidates(superclass, name, singleton, visited, candidates);
            }
        }
    }

    fn infer_initializer_call<'node>(
        &mut self,
        node: &Node<'node>,
        owner: &str,
        argument_nodes: &[Node<'node>],
        argument_types: &[Type],
    ) {
        let key = MethodKey {
            owner: Some(owner.to_owned()),
            name: "initialize".to_owned(),
            singleton: false,
        };
        if let Some(signature) = self.observe_call(&key, argument_types) {
            let _ = self.invoke_signature(
                node,
                "initialize",
                &signature,
                argument_nodes,
                argument_types,
            );
        }
    }

    fn implicit_method_key(&self, name: &str, environment: &Environment) -> MethodKey {
        if let Some(current) = &environment.method_key {
            MethodKey {
                owner: current.owner.clone(),
                name: name.to_owned(),
                singleton: current.singleton,
            }
        } else {
            MethodKey::top_level(name)
        }
    }

    fn receiver_method_key<'node>(
        &self,
        receiver_node: Option<&Node<'node>>,
        receiver_type: &Type,
        name: &str,
        environment: &Environment,
    ) -> Option<MethodKey> {
        let Type::Named(owner, _) = receiver_type else {
            return None;
        };
        let singleton = if receiver_node.is_some_and(|node| node.as_self_node().is_some()) {
            environment
                .method_key
                .as_ref()
                .is_some_and(|key| key.singleton)
        } else {
            receiver_node.is_some_and(|node| self.constant_reference_name(node).is_some())
        };
        Some(MethodKey {
            owner: Some(owner.clone()),
            name: name.to_owned(),
            singleton,
        })
    }

    fn ivar_key(&self, environment: &Environment, name: &str) -> Option<IvarKey> {
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

    fn observe_ivar(&mut self, environment: &Environment, name: String, actual: &Type) {
        let Some(key) = self.ivar_key(environment, &name) else {
            return;
        };
        let next = self
            .ivars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        self.ivars.insert(key, next);
    }

    fn ivar_type(&self, environment: &Environment, name: &str) -> Type {
        self.ivar_key(environment, name)
            .and_then(|key| self.ivars.get(&key).cloned())
            .unwrap_or(Type::Any)
    }

    fn lexical_owner(&self, environment: &Environment) -> Option<String> {
        environment
            .method_key
            .as_ref()
            .and_then(|key| key.owner.clone())
            .or_else(|| match &environment.self_type {
                Type::Named(owner, _) => Some(owner.clone()),
                _ => None,
            })
    }

    fn constant_key(&self, environment: &Environment, name: &str) -> String {
        let name = name.trim_start_matches("::");
        if name.contains("::") {
            return name.to_owned();
        }
        self.lexical_owner(environment)
            .map(|owner| format!("{owner}::{name}"))
            .unwrap_or_else(|| name.to_owned())
    }

    fn observe_constant(&mut self, environment: &Environment, name: String, actual: &Type) {
        let key = self.constant_key(environment, &name);
        let next = self
            .constants
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        self.constants.insert(key, next);
    }

    fn constant_type(&self, environment: &Environment, name: &str) -> Type {
        let name = name.trim_start_matches("::");
        if let Some(type_) = self.constants.get(&self.constant_key(environment, name)) {
            return type_.clone();
        }
        if let Some(type_) = self.constants.get(name) {
            return type_.clone();
        }
        let mut owner = self.lexical_owner(environment);
        let mut visited = BTreeSet::new();
        while let Some(current) = owner {
            if !visited.insert(current.clone()) {
                break;
            }
            let key = format!("{current}::{name}");
            if let Some(type_) = self.constants.get(&key) {
                return type_.clone();
            }
            owner = self
                .classes
                .get(&current)
                .and_then(|info| info.superclass.clone());
        }
        signature::parse_type(name)
    }

    fn class_var_owner(&self, environment: &Environment) -> String {
        self.lexical_owner(environment)
            .unwrap_or_else(|| "Object".to_owned())
    }

    fn observe_class_var(&mut self, environment: &Environment, name: String, actual: &Type) {
        let key = ClassVarKey {
            owner: self.class_var_owner(environment),
            name,
        };
        let next = self
            .class_vars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        self.class_vars.insert(key, next);
    }

    fn class_var_type(&self, environment: &Environment, name: &str) -> Type {
        let mut owner = Some(self.class_var_owner(environment));
        let mut visited = BTreeSet::new();
        while let Some(current) = owner {
            if !visited.insert(current.clone()) {
                break;
            }
            let key = ClassVarKey {
                owner: current.clone(),
                name: name.to_owned(),
            };
            if let Some(type_) = self.class_vars.get(&key) {
                return type_.clone();
            }
            owner = self
                .classes
                .get(&current)
                .and_then(|info| info.superclass.clone());
        }
        Type::Any
    }

    fn observe_global(&mut self, name: String, actual: &Type) {
        let next = self
            .globals
            .get(&name)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        self.globals.insert(name, next);
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
            "include" | "prepend" | "extend" | "alias_method" => Type::Nil,
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

        if receiver.is_never() {
            return Type::Never;
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
            Type::Proc(params, result) if matches!(name, "call" | "[]") => {
                for (index, (argument, expected)) in
                    site.argument_nodes.iter().zip(params).enumerate()
                {
                    if let Some(actual) = site.argument_types.get(index) {
                        self.check_assignable(argument, actual, expected);
                    }
                }
                result.as_ref().clone()
            }
            Type::Named(class, _) if name == "new" => Type::Named(class.clone(), Vec::new()),
            Type::Named(_, _) => self.eval_common_method(name),
            Type::Any
            | Type::Object
            | Type::Never
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
            "each_with_index" => {
                if let Some(block) = site.block {
                    let expected = vec![element.clone(), Type::Integer];
                    let _ = self.eval_block_node(block, &expected, environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "each" | "select" | "filter" | "filter_map" | "reject" | "sort" | "reverse"
            | "rotate" | "shuffle" => {
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
        outer: &mut Environment,
    ) -> Type {
        let Some(block) = node.as_block_node() else {
            return Type::Any;
        };
        let result = self.eval_block(&block, expected, outer);
        Self::block_value_type(&result)
    }

    fn block_value_type(result: &Eval) -> Type {
        let type_ = result
            .normal_type
            .clone()
            .unwrap_or(Type::Never)
            .join(&result.abrupt.next_type);
        if type_.is_never() {
            Type::Any
        } else {
            type_
        }
    }

    fn eval_block<'node>(
        &mut self,
        block: &ruby_prism::BlockNode<'node>,
        expected: &[Type],
        outer: &mut Environment,
    ) -> Eval {
        let captured = outer.clone();
        let mut environment = captured.clone();
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
        let result = if let Some(body) = block.body() {
            self.eval_node(&body, &mut environment)
        } else {
            Eval::value(Type::Nil)
        };
        self.propagate_block_locals(outer, &captured, &environment);
        result
    }

    fn propagate_block_locals(
        &self,
        outer: &mut Environment,
        captured: &Environment,
        block: &Environment,
    ) {
        for name in captured.locals.keys() {
            let type_ = captured.get(name).join(&block.get(name));
            outer.bind(name.clone(), type_);
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
