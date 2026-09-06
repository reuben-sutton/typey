use crate::diagnostic::Diagnostic;
use crate::directives::{is_typed_ignore, typed_mode, TypedMode};
use crate::prism;
use crate::signature::{self, AnnotationTable, AssertionKind, MethodSig};
use crate::types::{Type, TypeLattice};
use ruby_prism::{CallNode, ClassNode, DefNode, IfNode, Node, ParametersNode, UnlessNode, Visit};
use std::collections::{BTreeMap, BTreeSet};

const DEBUG_NODE_INTERVAL: usize = 1_000;

fn ivar_refinement_key(name: &str) -> String {
    format!("\u{1}ivar:{name}")
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MethodKey {
    owner: Option<String>,
    name: String,
    singleton: bool,
}

fn name_matches(name: &str, bare: &str) -> bool {
    name == bare || name == format!("T::{bare}")
}

#[derive(Clone, Debug, Default)]
struct ParameterShape {
    required_positional: usize,
    accepts_rest: bool,
    rest_index: Option<usize>,
    keywords: BTreeMap<String, bool>,
    accepts_keyword_rest: bool,
    has_block: bool,
    block_name: Option<String>,
}

impl ParameterShape {
    fn from_parameters<'node>(parameters: Option<ParametersNode<'node>>) -> Self {
        let Some(parameters) = parameters else {
            return Self::default();
        };
        let required_positional = parameters.requireds().len();
        let accepts_rest = parameters.rest().is_some()
            || parameters
                .keyword_rest()
                .is_some_and(|node| node.as_forwarding_parameter_node().is_some());
        let rest_index = parameters
            .rest()
            .map(|_| parameters.requireds().len() + parameters.optionals().len());
        let mut keywords = BTreeMap::new();
        for parameter in &parameters.keywords() {
            if let Some(required) = parameter.as_required_keyword_parameter_node() {
                keywords.insert(prism::constant_name(required.name()), true);
            } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                keywords.insert(prism::constant_name(optional.name()), false);
            }
        }
        Self {
            required_positional,
            accepts_rest,
            rest_index,
            keywords,
            accepts_keyword_rest: parameters.keyword_rest().is_some_and(|node| {
                node.as_keyword_rest_parameter_node().is_some()
                    || node.as_forwarding_parameter_node().is_some()
            }),
            has_block: parameters.block().is_some(),
            block_name: parameters
                .block()
                .and_then(|block| block.name())
                .map(prism::constant_name),
        }
    }
}

fn apply_parameter_shape(signature: &MethodSig, shape: &ParameterShape) -> MethodSig {
    if signature.param_names.is_empty() || signature.param_names.len() != signature.params.len() {
        return signature.clone();
    }

    let mut result = signature.clone();
    let mut params = Vec::new();
    let mut keywords = result.keywords.clone();
    let mut block = result.block.clone();
    for (name, type_) in signature.param_names.iter().zip(&signature.params) {
        let is_block_parameter =
            shape.has_block && (shape.block_name.as_deref() == Some(name.as_str()) || name == "&");
        if is_block_parameter {
            if let Some(proc_type) = optional_proc_type(type_) {
                block = Some(proc_type);
                continue;
            }
        }
        if let Some(required) = shape.keywords.get(name) {
            keywords.insert(
                name.clone(),
                signature::KeywordParam {
                    type_: type_.clone(),
                    required: *required,
                },
            );
            continue;
        }
        params.push(type_.clone());
    }
    result.params = params;
    result.param_names.clear();
    result.required_params = shape.required_positional.min(result.params.len());
    result.accepts_rest |= shape.accepts_rest;
    result.rest_index = shape.rest_index;
    result.accepts_keyword_rest |= shape.accepts_keyword_rest;
    result.keywords = keywords;
    result.block = block;
    result
}

fn optional_proc_type(type_: &Type) -> Option<Type> {
    match type_ {
        Type::Proc(_, _) => Some(type_.clone()),
        Type::Union(members)
            if members
                .iter()
                .all(|member| member.is_nil() || matches!(member, Type::Proc(_, _))) =>
        {
            members
                .iter()
                .find_map(|member| matches!(member, Type::Proc(_, _)).then(|| member.clone()))
        }
        _ => None,
    }
}

fn merge_method_signatures(signatures: &[MethodSig]) -> MethodSig {
    let Some(first) = signatures.first() else {
        return MethodSig::new(Vec::new(), Type::Any);
    };
    let parameter_count = signatures
        .iter()
        .map(|signature| signature.params.len())
        .max()
        .unwrap_or(0);
    let params = (0..parameter_count)
        .map(|index| {
            signatures.iter().fold(Type::Never, |current, signature| {
                current.join(signature.params.get(index).unwrap_or(&Type::Any))
            })
        })
        .collect();
    let mut keywords = BTreeMap::new();
    for signature in signatures {
        for (name, parameter) in &signature.keywords {
            let entry = keywords
                .entry(name.clone())
                .or_insert_with(|| signature::KeywordParam {
                    type_: Type::Never,
                    required: true,
                });
            entry.type_ = entry.type_.join(&parameter.type_);
            entry.required &= parameter.required;
        }
    }
    let return_type = signatures.iter().fold(Type::Never, |current, signature| {
        current.join(&signature.return_type)
    });
    MethodSig {
        params,
        param_names: Vec::new(),
        return_type,
        required_params: signatures
            .iter()
            .map(|signature| signature.required_params)
            .min()
            .unwrap_or(first.required_params),
        accepts_rest: signatures.iter().any(|signature| signature.accepts_rest),
        rest_index: signatures
            .iter()
            .find(|signature| signature.accepts_rest)
            .and_then(|signature| signature.rest_index),
        keywords,
        accepts_keyword_rest: signatures
            .iter()
            .any(|signature| signature.accepts_keyword_rest),
        type_parameters: signatures
            .iter()
            .flat_map(|signature| signature.type_parameters.iter().cloned())
            .fold(Vec::new(), |mut names, name| {
                if !names.contains(&name) {
                    names.push(name);
                }
                names
            }),
        block: signatures
            .iter()
            .filter_map(|signature| signature.block.as_ref())
            .cloned()
            .reduce(|current, block| current.join(&block)),
        is_void: signatures.iter().all(|signature| signature.is_void),
    }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AccessorKind {
    Reader,
    Writer,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ClassVarKey {
    owner: String,
    name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SharedKey {
    Ivar(IvarKey),
    Constant(String),
    ClassVar(ClassVarKey),
    Global(String),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GenericMember {
    index: usize,
    fixed: Option<Type>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ClassInfo {
    superclass: Option<String>,
    includes: Vec<String>,
    prepends: Vec<String>,
    extends: Vec<String>,
    type_members: BTreeMap<String, GenericMember>,
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
    /// Emit phase and progress information to stderr while checking.
    pub debug: bool,
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            strictness: Strictness::Ignore,
            debug: false,
        }
    }
}

fn strictness_rank(strictness: Strictness) -> u8 {
    match strictness {
        Strictness::Ignore => 0,
        Strictness::Strict => 1,
        Strictness::Strong => 2,
    }
}

/// A type recorded for an expression, useful to editors and debugging tools.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum UntypedOrigin {
    /// The expression itself contains an explicit `T.untyped` annotation.
    ExplicitAnnotation,
    /// The expression is the result of `T.unsafe`.
    Unsafe,
    /// The expression was produced by an explicit source or RBI signature.
    DeclaredSignature,
    /// The expression was produced by an inferred method summary.
    InferredMethod,
    /// The expression came from a call without a resolved method signature.
    FallbackCall,
    /// The expression inherited `T.untyped` from a child or surrounding value.
    Propagated,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferredType {
    pub start: usize,
    pub end: usize,
    pub type_: Type,
    pub untyped_origin: Option<UntypedOrigin>,
    pub is_send: bool,
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

    fn flow(&self) -> Flow {
        let mut flow = Flow::empty();
        for (kind, type_) in [
            (FlowKind::Return, &self.return_type),
            (FlowKind::Raise, &self.raise_type),
            (FlowKind::Break, &self.break_type),
            (FlowKind::Next, &self.next_type),
            (FlowKind::Retry, &self.retry_type),
        ] {
            if !type_.is_never() {
                flow = flow.union(Flow::abrupt(kind));
            }
        }
        flow
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

struct KeywordArgument<'node> {
    name: String,
    node: Node<'node>,
    type_: Type,
}

#[derive(Default)]
struct CallArguments<'node> {
    argument_nodes: Vec<Node<'node>>,
    argument_types: Vec<Type>,
    argument_indices: Vec<usize>,
    positional_indices: Vec<usize>,
    positional_types: Vec<Type>,
    keyword_arguments: Vec<KeywordArgument<'node>>,
    has_keyword_splat: bool,
    has_dynamic_positional_splat: bool,
    dynamic_positional_splat_types: Vec<Type>,
    has_dynamic_keyword_splat: bool,
    has_unknown_positional_splat: bool,
    has_unknown_keyword_splat: bool,
    /// The call uses Ruby's `...` forwarding form. There is no concrete
    /// argument list at this syntax site; it is the caller's complete
    /// positional, keyword, and block argument set.
    forwards_arguments: bool,
}

struct CallArgumentEvaluation<'node> {
    arguments: CallArguments<'node>,
    abrupt: OutcomeTypes,
    abrupt_flow: Flow,
    all_normal: bool,
}

struct IndexAccess<'node> {
    receiver_type: Type,
    arguments: CallArguments<'node>,
    abrupt: OutcomeTypes,
    abrupt_flow: Flow,
    all_normal: bool,
}

enum IndexAssignmentKind {
    Operator(String),
    And,
    Or,
}

enum CallAssignmentKind {
    Operator(String),
    And,
    Or,
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
    rest_index: Option<usize>,
    keywords: BTreeMap<String, Option<Type>>,
    yield_params: Vec<Option<Type>>,
    block_return_type: Option<Type>,
    block: Option<Type>,
    required_keywords: BTreeSet<String>,
    return_type: Option<Type>,
    return_terminates: bool,
    required_params: usize,
    accepts_rest: bool,
    accepts_keyword_rest: bool,
    is_void: bool,
    explicit: bool,
    overloads: Vec<MethodSig>,
}

impl MethodState {
    fn explicit_overloads(signatures: &[MethodSig]) -> Self {
        let signature = merge_method_signatures(signatures);
        let (yield_params, block_return_type) = signature
            .block
            .as_ref()
            .and_then(|block| match block {
                Type::Proc(parameters, return_type) => Some((
                    parameters.iter().cloned().map(Some).collect(),
                    Some((**return_type).clone()),
                )),
                _ => None,
            })
            .unwrap_or_default();
        Self {
            params: signature.params.iter().cloned().map(Some).collect(),
            rest_index: signature.rest_index,
            keywords: signature
                .keywords
                .iter()
                .map(|(name, parameter)| (name.clone(), Some(parameter.type_.clone())))
                .collect(),
            yield_params,
            block_return_type,
            block: signature.block.clone(),
            required_keywords: signature
                .keywords
                .iter()
                .filter_map(|(name, parameter)| parameter.required.then_some(name.clone()))
                .collect(),
            return_type: Some(signature.return_type.clone()),
            return_terminates: signature.return_type.is_never(),
            required_params: signature.required_params,
            accepts_rest: signature.accepts_rest,
            accepts_keyword_rest: signature.accepts_keyword_rest,
            is_void: signature.is_void,
            explicit: true,
            overloads: signatures.to_vec(),
        }
    }

    fn inferred<'node>(parameters: Option<ParametersNode<'node>>) -> Self {
        let mut params = Vec::new();
        let mut keywords = BTreeMap::new();
        let mut required_keywords = BTreeSet::new();
        let mut required_params = 0;
        let mut rest_index = None;

        if let Some(parameters) = parameters {
            for _ in &parameters.requireds() {
                params.push(None);
                required_params += 1;
            }
            for _ in &parameters.optionals() {
                params.push(None);
            }
            let accepts_rest = parameters.rest().is_some()
                || parameters
                    .keyword_rest()
                    .is_some_and(|node| node.as_forwarding_parameter_node().is_some());
            if accepts_rest {
                rest_index = Some(params.len());
                params.push(None);
            }
            for _ in &parameters.posts() {
                params.push(None);
                required_params += 1;
            }
            for parameter in &parameters.keywords() {
                if let Some(required) = parameter.as_required_keyword_parameter_node() {
                    let name = prism::constant_name(required.name());
                    keywords.insert(name.clone(), None);
                    required_keywords.insert(name);
                } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                    keywords.insert(prism::constant_name(optional.name()), None);
                }
            }
            return Self {
                params,
                rest_index,
                keywords,
                yield_params: Vec::new(),
                block_return_type: None,
                block: None,
                required_keywords,
                return_type: None,
                return_terminates: false,
                required_params,
                accepts_rest,
                accepts_keyword_rest: parameters.keyword_rest().is_some_and(|node| {
                    node.as_keyword_rest_parameter_node().is_some()
                        || node.as_forwarding_parameter_node().is_some()
                }),
                is_void: false,
                explicit: false,
                overloads: Vec::new(),
            };
        }

        Self {
            params,
            rest_index,
            keywords,
            yield_params: Vec::new(),
            block_return_type: None,
            block: None,
            required_keywords,
            return_type: None,
            return_terminates: false,
            required_params,
            accepts_rest: false,
            accepts_keyword_rest: false,
            is_void: false,
            explicit: false,
            overloads: Vec::new(),
        }
    }

    fn inferred_accessor(kind: AccessorKind) -> Self {
        let mut state = Self::inferred(None);
        state.return_type = Some(Type::Any);
        if kind == AccessorKind::Writer {
            state.params = vec![Some(Type::Any)];
            state.required_params = 1;
        }
        state
    }

    fn body_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            param_names: Vec::new(),
            return_type: Type::Any,
            required_params: self.required_params,
            accepts_rest: self.accepts_rest,
            rest_index: self.rest_index,
            keywords: self
                .keywords
                .iter()
                .map(|(name, type_)| {
                    (
                        name.clone(),
                        signature::KeywordParam {
                            type_: type_.clone().unwrap_or(Type::Any),
                            required: self.required_keywords.contains(name),
                        },
                    )
                })
                .collect(),
            accepts_keyword_rest: self.accepts_keyword_rest,
            type_parameters: Vec::new(),
            block: self.block.clone(),
            is_void: false,
        }
    }

    fn call_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            param_names: Vec::new(),
            return_type: self.return_type.clone().unwrap_or(Type::Never),
            required_params: self.required_params,
            accepts_rest: self.accepts_rest,
            rest_index: self.rest_index,
            keywords: self
                .keywords
                .iter()
                .map(|(name, type_)| {
                    (
                        name.clone(),
                        signature::KeywordParam {
                            type_: type_.clone().unwrap_or(Type::Any),
                            required: self.required_keywords.contains(name),
                        },
                    )
                })
                .collect(),
            accepts_keyword_rest: self.accepts_keyword_rest,
            type_parameters: Vec::new(),
            block: self.block.clone().or_else(|| {
                (!self.yield_params.is_empty() || self.block_return_type.is_some()).then(|| {
                    Type::Proc(
                        self.block_parameters(),
                        Box::new(self.block_return_type.clone().unwrap_or(Type::Any)),
                    )
                })
            }),
            is_void: self.is_void,
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

    fn observe_arguments(&mut self, actuals: &[Type]) -> bool {
        if self.explicit {
            return false;
        }
        let Some(rest_index) = self.rest_index else {
            return actuals
                .iter()
                .enumerate()
                .fold(false, |changed, (index, actual)| {
                    self.observe_argument(index, actual) || changed
                });
        };

        let post_count = self.params.len().saturating_sub(rest_index + 1);
        let has_all_posts = actuals.len() >= rest_index + post_count;
        let post_start = if has_all_posts {
            actuals.len().saturating_sub(post_count)
        } else {
            actuals.len()
        };
        let mut changed = false;
        for (index, actual) in actuals.iter().enumerate() {
            let slot_index = if index < rest_index {
                index
            } else if has_all_posts && index >= post_start {
                rest_index + 1 + index - post_start
            } else {
                rest_index
            };
            changed |= self.observe_argument(slot_index, actual);
        }
        changed
    }

    fn observe_keyword(&mut self, name: &str, actual: &Type) -> bool {
        if self.explicit {
            return false;
        }
        let Some(slot) = self.keywords.get_mut(name) else {
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

    fn block_parameters(&self) -> Vec<Type> {
        if let Some(Type::Proc(parameters, _)) = &self.block {
            return parameters.clone();
        }
        self.yield_params
            .iter()
            .map(|type_| type_.clone().unwrap_or(Type::Any))
            .collect()
    }

    fn block_result_type(&self) -> Type {
        self.block
            .as_ref()
            .and_then(|block| match block {
                Type::Proc(_, result) => Some((**result).clone()),
                _ => None,
            })
            .or_else(|| self.block_return_type.clone())
            .unwrap_or(Type::Any)
    }

    fn observe_yield_arguments(&mut self, actual: &[Type]) -> bool {
        let mut changed = false;
        for (index, actual) in actual.iter().enumerate() {
            if index >= self.yield_params.len() {
                self.yield_params.push(Some(actual.clone()));
                changed = true;
                continue;
            }
            let slot = &mut self.yield_params[index];
            let next = slot
                .as_ref()
                .map_or_else(|| actual.clone(), |current| current.join(actual));
            if slot.as_ref() != Some(&next) {
                *slot = Some(next);
                changed = true;
            }
        }
        changed
    }

    fn observe_block_return(&mut self, actual: &Type) -> bool {
        let next = self
            .block_return_type
            .as_ref()
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.block_return_type.as_ref() == Some(&next) {
            false
        } else {
            self.block_return_type = Some(next);
            true
        }
    }
}

struct MethodRegistrar<'a> {
    source: &'a [u8],
    methods: &'a mut BTreeMap<MethodKey, MethodState>,
    definitions: &'a mut BTreeMap<usize, MethodKey>,
    parameter_shapes: &'a mut BTreeMap<usize, ParameterShape>,
    classes: &'a mut BTreeMap<String, ClassInfo>,
    aliases: &'a mut BTreeMap<MethodKey, MethodKey>,
    accessors: &'a mut BTreeMap<MethodKey, AccessorKind>,
    attribute_annotations: &'a BTreeMap<usize, Vec<MethodSig>>,
    class_type_parameters: &'a BTreeMap<usize, Vec<String>>,
    type_aliases: &'a mut BTreeMap<String, Type>,
    constants: &'a mut BTreeMap<String, Type>,
    class_stack: Vec<String>,
    singleton_stack: Vec<String>,
    method_depth: usize,
}

impl<'pr> Visit<'pr> for MethodRegistrar<'_> {
    fn visit_def_node(&mut self, node: &DefNode<'pr>) {
        let name = prism::constant_name(node.name());
        let definition_start = prism::span(&node.as_node()).0;
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
        self.definitions.insert(definition_start, key.clone());
        self.parameter_shapes.insert(
            definition_start,
            ParameterShape::from_parameters(node.parameters()),
        );
        self.methods
            .entry(key)
            .or_insert_with(|| MethodState::inferred(node.parameters()));
        self.method_depth += 1;
        ruby_prism::visit_def_node(self, node);
        self.method_depth -= 1;
    }

    fn visit_class_node(&mut self, node: &ClassNode<'pr>) {
        let name = self.scope_name(&node.constant_path());
        let superclass = node
            .superclass()
            .map(|superclass| self.scope_reference(&superclass));
        let info = self.classes.entry(name.clone()).or_default();
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

    fn visit_constant_path_write_node(&mut self, node: &ruby_prism::ConstantPathWriteNode<'pr>) {
        let target = node.target();
        let name = self.constant_assignment_name(&prism::text(self.source, &target.as_node()));
        if let Some(type_) = self.parse_typed_constant(&node.value()) {
            self.constants.insert(name.clone(), type_);
        }
        self.register_type_alias(name, &node.value());
        ruby_prism::visit_constant_path_write_node(self, node);
    }

    fn visit_constant_write_node(&mut self, node: &ruby_prism::ConstantWriteNode<'pr>) {
        let constant_name = prism::constant_name(node.name());
        if let Some(owner) = self.class_stack.last() {
            if let Some(member) = self.parse_generic_member(&node.value()) {
                let info = self.classes.entry(owner.clone()).or_default();
                let index = info.type_members.len();
                info.type_members
                    .insert(constant_name.clone(), GenericMember { index, ..member });
            }
        }
        let name = self.constant_assignment_name(&constant_name);
        if let Some(type_) = self.parse_typed_constant(&node.value()) {
            self.constants.insert(name.clone(), type_);
        }
        self.register_type_alias(name, &node.value());
        ruby_prism::visit_constant_write_node(self, node);
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
                    let module = self.scope_reference_text(module);
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
                                self.aliases.insert(
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
                if matches!(
                    name.as_str(),
                    "attr_reader" | "attr_writer" | "attr_accessor"
                ) {
                    let owner = self
                        .singleton_stack
                        .last()
                        .cloned()
                        .or_else(|| self.class_stack.last().cloned());
                    let singleton = self.singleton_stack.last().is_some();
                    let signatures = self
                        .attribute_annotations
                        .get(&prism::span(&node.as_node()).0);
                    for attribute in &arguments {
                        let add_accessor =
                            |registrar: &mut Self, name: String, kind: AccessorKind| {
                                let key = MethodKey {
                                    owner: owner.clone(),
                                    name,
                                    singleton,
                                };
                                registrar.accessors.insert(key.clone(), kind);
                                let state = signatures.map_or_else(
                                    || MethodState::inferred_accessor(kind),
                                    |signatures| MethodState::explicit_overloads(signatures),
                                );
                                registrar.methods.entry(key).or_insert(state);
                            };
                        match name.as_str() {
                            "attr_reader" => {
                                add_accessor(self, attribute.clone(), AccessorKind::Reader)
                            }
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

    fn scope_reference<'node>(&self, node: &Node<'node>) -> String {
        self.scope_reference_text(&prism::text(self.source, node))
    }

    fn scope_reference_text(&self, text: &str) -> String {
        let absolute = text.trim_start().starts_with("::");
        let raw = text.trim().trim_start_matches("::");
        if absolute || raw.contains("::") || self.class_stack.is_empty() {
            raw.to_owned()
        } else {
            let candidate = format!(
                "{}::{raw}",
                self.class_stack.last().expect("stack is not empty")
            );
            if self.classes.contains_key(&candidate) {
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
            self.type_aliases.insert(name, type_);
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

/// Check a source buffer with direct ruby-prism parsing.
#[must_use]
pub fn check(source: &str, config: CheckerConfig) -> CheckResult {
    let strictness_ranges = source_strictness_ranges(source);
    let (mut result, parse_diagnostics) =
        check_with_policies(source, config, &[], &[], &strictness_ranges);
    if typed_mode(source) == Some(TypedMode::False) {
        result
            .diagnostics
            .retain(|diagnostic| parse_diagnostics.contains(diagnostic));
    }
    result
}

pub(crate) fn check_with_rbi_ranges(
    source: &str,
    config: CheckerConfig,
    rbi_ranges: &[(usize, usize)],
) -> CheckResult {
    let strictness_ranges = source_strictness_ranges(source);
    check_with_policies(source, config, rbi_ranges, &[], &strictness_ranges).0
}

pub(crate) fn check_with_policies(
    source: &str,
    config: CheckerConfig,
    rbi_ranges: &[(usize, usize)],
    builtin_rbi_ranges: &[(usize, usize)],
    strictness_ranges: &[(usize, usize, Strictness)],
) -> (CheckResult, Vec<Diagnostic>) {
    if is_typed_ignore(source) {
        return (CheckResult::default(), Vec::new());
    }

    let bytes = source.as_bytes();
    if config.debug {
        eprintln!("[typey] Prism parsing {} bytes", bytes.len());
    }
    let parsed = prism::parse(bytes);
    let root = parsed.node();
    let annotations = signature::collect_for_ast(source, &root);
    let diagnostics = parsed
        .errors()
        .map(|error| {
            let location = error.location();
            let (start, end) = prism::location_span(&location);
            Diagnostic::error(bytes, error.message(), start, end)
        })
        .collect::<Vec<_>>();
    if config.debug {
        eprintln!(
            "[typey] Prism parse complete: {} syntax diagnostics, {} method annotations, {} inline assertions",
            diagnostics.len(),
            annotations.method_annotations.len(),
            annotations.assertions.len()
        );
    }
    let analyzer = Analyzer {
        source: bytes,
        line_map: prism::LineMap::new(bytes),
        annotations,
        config,
        methods: BTreeMap::new(),
        definitions: BTreeMap::new(),
        parameter_shapes: BTreeMap::new(),
        classes: BTreeMap::new(),
        aliases: BTreeMap::new(),
        accessors: BTreeMap::new(),
        type_aliases: BTreeMap::new(),
        ivars: BTreeMap::new(),
        constants: BTreeMap::new(),
        class_vars: BTreeMap::new(),
        globals: BTreeMap::new(),
        report: true,
        seed_calls: false,
        rbi_ranges: rbi_ranges.to_vec(),
        builtin_rbi_ranges: builtin_rbi_ranges.to_vec(),
        strictness_ranges: strictness_ranges.to_vec(),
        filter_method_bodies: false,
        active_methods: BTreeSet::new(),
        changed_methods: BTreeSet::new(),
        pending_returns: BTreeMap::new(),
        collecting_returns: false,
        method_callers: BTreeMap::new(),
        method_shared_reads: BTreeMap::new(),
        shared_readers: BTreeMap::new(),
        changed_shared: BTreeSet::new(),
        debug_phase: "idle",
        debug_round: 0,
        debug_nodes: 0,
        defer_inline_assertions: false,
        expected_return_type: None,
        diagnostics: diagnostics.clone(),
        types: Vec::new(),
        untyped_origins: BTreeMap::new(),
    };
    let result = analyzer.run(&root);
    (result, diagnostics)
}

fn source_strictness_ranges(source: &str) -> Vec<(usize, usize, Strictness)> {
    let strictness = match typed_mode(source) {
        Some(TypedMode::Strict) => Strictness::Strict,
        Some(TypedMode::Strong) => Strictness::Strong,
        _ => return Vec::new(),
    };
    vec![(0, source.len(), strictness)]
}

struct Analyzer<'src> {
    source: &'src [u8],
    line_map: prism::LineMap,
    annotations: AnnotationTable,
    config: CheckerConfig,
    methods: BTreeMap<MethodKey, MethodState>,
    definitions: BTreeMap<usize, MethodKey>,
    parameter_shapes: BTreeMap<usize, ParameterShape>,
    classes: BTreeMap<String, ClassInfo>,
    aliases: BTreeMap<MethodKey, MethodKey>,
    accessors: BTreeMap<MethodKey, AccessorKind>,
    type_aliases: BTreeMap<String, Type>,
    ivars: BTreeMap<IvarKey, Type>,
    constants: BTreeMap<String, Type>,
    class_vars: BTreeMap<ClassVarKey, Type>,
    globals: BTreeMap<String, Type>,
    report: bool,
    seed_calls: bool,
    rbi_ranges: Vec<(usize, usize)>,
    builtin_rbi_ranges: Vec<(usize, usize)>,
    strictness_ranges: Vec<(usize, usize, Strictness)>,
    filter_method_bodies: bool,
    active_methods: BTreeSet<MethodKey>,
    changed_methods: BTreeSet<MethodKey>,
    pending_returns: BTreeMap<MethodKey, (Type, bool)>,
    collecting_returns: bool,
    method_callers: BTreeMap<MethodKey, BTreeSet<MethodKey>>,
    method_shared_reads: BTreeMap<MethodKey, BTreeSet<SharedKey>>,
    shared_readers: BTreeMap<SharedKey, BTreeSet<MethodKey>>,
    changed_shared: BTreeSet<SharedKey>,
    debug_phase: &'static str,
    debug_round: usize,
    debug_nodes: usize,
    defer_inline_assertions: bool,
    expected_return_type: Option<Type>,
    diagnostics: Vec<Diagnostic>,
    types: Vec<InferredType>,
    untyped_origins: BTreeMap<(usize, usize), UntypedOrigin>,
}

impl<'src> Analyzer<'src> {
    fn is_send_node(node: &Node<'_>) -> bool {
        node.as_call_node().is_some()
            || node.as_call_and_write_node().is_some()
            || node.as_call_operator_write_node().is_some()
            || node.as_call_or_write_node().is_some()
            || node.as_class_variable_operator_write_node().is_some()
            || node.as_constant_operator_write_node().is_some()
            || node.as_constant_path_operator_write_node().is_some()
            || node.as_global_variable_operator_write_node().is_some()
            || node.as_index_and_write_node().is_some()
            || node.as_index_operator_write_node().is_some()
            || node.as_index_or_write_node().is_some()
            || node.as_instance_variable_operator_write_node().is_some()
            || node.as_local_variable_operator_write_node().is_some()
            || node.as_yield_node().is_some()
            || node.as_super_node().is_some()
            || node.as_forwarding_super_node().is_some()
    }

    fn normal_type(result: Eval) -> Type {
        result.normal_type.unwrap_or(Type::Never)
    }

    fn class_object_type(name: &str) -> Type {
        Type::Named("Class".to_owned(), vec![Type::named(name)])
    }

    fn class_object_instance_type(type_: &Type) -> Option<Type> {
        match type_ {
            Type::Named(name, arguments) if name_matches(name, "Class") => {
                arguments.first().cloned()
            }
            _ => None,
        }
    }

    fn named_type_name(type_: &Type) -> Option<String> {
        match type_ {
            Type::Named(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    fn class_object_owner(type_: &Type) -> Option<String> {
        Self::class_object_instance_type(type_)
            .and_then(|instance| Self::named_type_name(&instance))
    }

    fn class_object_value_type(type_: &Type) -> Option<Type> {
        let instance = Self::class_object_instance_type(type_)?;
        let builtin = match &instance {
            Type::Named(name, arguments) if arguments.is_empty() => {
                // A project namespace may define a class whose short name
                // matches a Ruby primitive (for example
                // `Spoom::Model::Symbol`).  Only the actual top-level
                // builtins have structural primitive semantics; otherwise
                // `Some(Symbol.new)` would incorrectly become the language's
                // built-in `Symbol` type.
                match name.as_str() {
                    "Integer" => Some(Type::Integer),
                    "Float" => Some(Type::Float),
                    "String" => Some(Type::String),
                    "Symbol" => Some(Type::Symbol),
                    "NilClass" => Some(Type::Nil),
                    "TrueClass" => Some(Type::True),
                    "FalseClass" => Some(Type::False),
                    "Object" | "BasicObject" => Some(Type::Object),
                    _ => None,
                }
            }
            _ => None,
        };
        Some(builtin.unwrap_or(instance))
    }

    fn receiver_instance_type(type_: &Type) -> Type {
        if let Some(instance) = Self::class_object_instance_type(type_) {
            return instance;
        }
        if let Type::Union(members) = type_ {
            return Type::union(members.iter().map(Self::receiver_instance_type));
        }
        type_.clone()
    }

    fn instance_self_type(&self, owner: &str) -> Type {
        let hosts = self
            .classes
            .iter()
            .filter_map(|(candidate, info)| {
                info.includes
                    .iter()
                    .any(|included| included == owner || self.nominal_names_match(included, owner))
                    .then(|| Type::named(candidate.clone()))
            })
            .collect::<Vec<_>>();
        if hosts.is_empty() {
            Type::named(owner)
        } else {
            Type::union(hosts)
        }
    }

    fn substitute_instance_type(type_: &Type, receiver_type: Option<&Type>) -> Type {
        match type_ {
            Type::Named(name, arguments) if name == "instance" && arguments.is_empty() => {
                receiver_type.map_or_else(|| type_.clone(), Self::receiver_instance_type)
            }
            Type::AttachedClass => {
                receiver_type.map_or_else(|| Type::AttachedClass, Self::receiver_instance_type)
            }
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| Self::substitute_instance_type(argument, receiver_type))
                    .collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(Self::substitute_instance_type(
                element,
                receiver_type,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(Self::substitute_instance_type(key, receiver_type)),
                Box::new(Self::substitute_instance_type(value, receiver_type)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| Self::substitute_instance_type(element, receiver_type))
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| Self::substitute_instance_type(parameter, receiver_type))
                    .collect(),
                Box::new(Self::substitute_instance_type(result, receiver_type)),
            ),
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| Self::substitute_instance_type(member, receiver_type)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| Self::substitute_instance_type(member, receiver_type)),
            ),
            other => other.clone(),
        }
    }

    fn contains_type_parameter(type_: &Type, names: &BTreeSet<String>) -> bool {
        match type_ {
            Type::TypeVar(name) => names.contains(name),
            Type::Named(_, arguments) => arguments
                .iter()
                .any(|argument| Self::contains_type_parameter(argument, names)),
            Type::Array(element) => Self::contains_type_parameter(element, names),
            Type::Hash(key, value) => {
                Self::contains_type_parameter(key, names)
                    || Self::contains_type_parameter(value, names)
            }
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| Self::contains_type_parameter(element, names)),
            Type::Proc(parameters, result) => {
                parameters
                    .iter()
                    .any(|parameter| Self::contains_type_parameter(parameter, names))
                    || Self::contains_type_parameter(result, names)
            }
            Type::Union(members) | Type::Intersection(members) => members
                .iter()
                .any(|member| Self::contains_type_parameter(member, names)),
            _ => false,
        }
    }

    fn infer_type_parameter_bindings(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
        block_return_type: Option<&Type>,
    ) -> BTreeMap<String, Type> {
        let names = signature
            .type_parameters
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut bindings = BTreeMap::new();
        if names.is_empty() {
            return bindings;
        }

        let positional_types = if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        for (index, actual) in positional_types.iter().enumerate() {
            if let Some(expected) = signature.positional_type(index, positional_types.len()) {
                self.collect_type_parameter_binding(expected, actual, &names, &mut bindings);
            }
        }
        if signature.accepts_rest && signature.rest_index == Some(0) {
            if let Some(expected) = signature.params.first() {
                for splat_type in &arguments.dynamic_positional_splat_types {
                    if let Type::Array(element) = splat_type {
                        self.collect_type_parameter_binding(
                            expected,
                            element,
                            &names,
                            &mut bindings,
                        );
                    }
                }
            }
        }
        if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            for argument in &arguments.keyword_arguments {
                if let Some(expected) = signature.keywords.get(&argument.name) {
                    self.collect_type_parameter_binding(
                        &expected.type_,
                        &argument.type_,
                        &names,
                        &mut bindings,
                    );
                }
            }
        }
        if let (Some(Type::Proc(_, expected_return)), Some(actual_return)) =
            (signature.block.as_ref(), block_return_type)
        {
            self.collect_type_parameter_binding(
                expected_return,
                actual_return,
                &names,
                &mut bindings,
            );
        }
        bindings
    }

    fn collect_type_parameter_binding(
        &self,
        expected: &Type,
        actual: &Type,
        names: &BTreeSet<String>,
        bindings: &mut BTreeMap<String, Type>,
    ) {
        match expected {
            Type::TypeVar(name) if names.contains(name) => {
                bindings
                    .entry(name.clone())
                    .and_modify(|current| *current = current.join(actual))
                    .or_insert_with(|| actual.clone());
            }
            Type::Union(members) => {
                let fixed_match = members.iter().any(|member| {
                    !Self::contains_type_parameter(member, names)
                        && self.is_assignable(actual, member)
                });
                if !fixed_match {
                    for member in members {
                        if Self::contains_type_parameter(member, names) {
                            self.collect_type_parameter_binding(member, actual, names, bindings);
                        }
                    }
                }
            }
            Type::Intersection(members) => {
                for member in members {
                    self.collect_type_parameter_binding(member, actual, names, bindings);
                }
            }
            Type::Array(expected) => {
                if let Type::Array(actual) = actual {
                    self.collect_type_parameter_binding(expected, actual, names, bindings);
                }
            }
            Type::Hash(expected_key, expected_value) => {
                if let Type::Hash(actual_key, actual_value) = actual {
                    self.collect_type_parameter_binding(expected_key, actual_key, names, bindings);
                    self.collect_type_parameter_binding(
                        expected_value,
                        actual_value,
                        names,
                        bindings,
                    );
                }
            }
            Type::Tuple(expected_elements) => {
                if let Type::Tuple(actual_elements) = actual {
                    for (expected, actual) in expected_elements.iter().zip(actual_elements) {
                        self.collect_type_parameter_binding(expected, actual, names, bindings);
                    }
                }
            }
            Type::Proc(expected_parameters, expected_result) => {
                if let Type::Proc(actual_parameters, actual_result) = actual {
                    for (expected, actual) in expected_parameters.iter().zip(actual_parameters) {
                        self.collect_type_parameter_binding(expected, actual, names, bindings);
                    }
                    self.collect_type_parameter_binding(
                        expected_result,
                        actual_result,
                        names,
                        bindings,
                    );
                }
            }
            Type::Named(expected_name, expected_arguments) => {
                if expected_arguments.len() == 1 && name_matches(expected_name, "Enumerable") {
                    let element = match actual {
                        Type::Array(element) => Some((**element).clone()),
                        Type::Tuple(elements) => Some(Type::union(elements.iter().cloned())),
                        Type::Hash(key, value) => {
                            Some(Type::Tuple(vec![(**key).clone(), (**value).clone()]))
                        }
                        Type::Named(_, _) => {
                            self.generic_member_binding("Enumerable::Elem", Some(actual))
                        }
                        _ => None,
                    };
                    if let Some(element) = element {
                        self.collect_type_parameter_binding(
                            &expected_arguments[0],
                            &element,
                            names,
                            bindings,
                        );
                        return;
                    }
                }
                if let Type::Named(actual_name, actual_arguments) = actual {
                    if name_matches(expected_name, actual_name)
                        || name_matches(actual_name, expected_name)
                    {
                        for (expected, actual) in expected_arguments.iter().zip(actual_arguments) {
                            self.collect_type_parameter_binding(expected, actual, names, bindings);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn substitute_type_parameters(
        type_: &Type,
        bindings: &BTreeMap<String, Type>,
        names: &BTreeSet<String>,
    ) -> Type {
        match type_ {
            Type::TypeVar(name) if names.contains(name) => {
                bindings.get(name).cloned().unwrap_or_else(|| type_.clone())
            }
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| Self::substitute_type_parameters(argument, bindings, names))
                    .collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(Self::substitute_type_parameters(
                element, bindings, names,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(Self::substitute_type_parameters(key, bindings, names)),
                Box::new(Self::substitute_type_parameters(value, bindings, names)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| Self::substitute_type_parameters(element, bindings, names))
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| Self::substitute_type_parameters(parameter, bindings, names))
                    .collect(),
                Box::new(Self::substitute_type_parameters(result, bindings, names)),
            ),
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| Self::substitute_type_parameters(member, bindings, names)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| Self::substitute_type_parameters(member, bindings, names)),
            ),
            other => other.clone(),
        }
    }

    fn generic_member_binding(&self, name: &str, receiver_type: Option<&Type>) -> Option<Type> {
        let receiver_type = receiver_type.map(Self::receiver_instance_type)?;
        if let Type::Union(members) = &receiver_type {
            let mut bindings = members
                .iter()
                .filter_map(|member| self.generic_member_binding(name, Some(member)));
            let first = bindings.next()?;
            return Some(bindings.fold(first, |current, member| current.join(&member)));
        }
        let Type::Named(receiver_owner, arguments) = receiver_type else {
            return None;
        };
        let (declared_owner, member_name) = name.rsplit_once("::")?;
        let info = self.classes.get(declared_owner)?;
        let related = receiver_owner == declared_owner
            || self
                .classes
                .get(&receiver_owner)
                .is_some_and(|receiver_info| {
                    receiver_info
                        .includes
                        .iter()
                        .any(|owner| owner == declared_owner)
                        || receiver_info
                            .prepends
                            .iter()
                            .any(|owner| owner == declared_owner)
                        || receiver_info
                            .extends
                            .iter()
                            .any(|owner| owner == declared_owner)
                })
            || self.nominal_subtype(&receiver_owner, declared_owner);
        if !related {
            return None;
        }
        let member = info.type_members.get(member_name)?;
        if let Some(fixed) = &member.fixed {
            return Some(self.resolve_type_names(fixed, Some(declared_owner)));
        }
        Some(arguments.get(member.index).cloned().unwrap_or(Type::Any))
    }

    fn is_open_generic_member(&self, name: &str, receiver_type: Option<&Type>) -> bool {
        let Some((declared_owner, member_name)) = name.rsplit_once("::") else {
            return false;
        };
        self.classes
            .get(declared_owner)
            .and_then(|info| info.type_members.get(member_name))
            .is_some_and(|member| {
                member.fixed.is_none()
                    && self
                        .generic_member_binding(name, receiver_type)
                        .is_some_and(|type_| type_.is_any())
            })
    }

    fn contains_open_generic_member(&self, type_: &Type, receiver_type: Option<&Type>) -> bool {
        match type_ {
            Type::TypeVar(name) => self.is_open_generic_member(name, receiver_type),
            Type::Named(_, arguments) => arguments
                .iter()
                .any(|argument| self.contains_open_generic_member(argument, receiver_type)),
            Type::Array(element) => self.contains_open_generic_member(element, receiver_type),
            Type::Hash(key, value) => {
                self.contains_open_generic_member(key, receiver_type)
                    || self.contains_open_generic_member(value, receiver_type)
            }
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| self.contains_open_generic_member(element, receiver_type)),
            Type::Proc(parameters, result) => {
                parameters
                    .iter()
                    .any(|parameter| self.contains_open_generic_member(parameter, receiver_type))
                    || self.contains_open_generic_member(result, receiver_type)
            }
            Type::Union(members) | Type::Intersection(members) => members
                .iter()
                .any(|member| self.contains_open_generic_member(member, receiver_type)),
            _ => false,
        }
    }

    fn collect_generic_member_binding(
        &self,
        expected: &Type,
        actual: &Type,
        receiver_type: Option<&Type>,
        bindings: &mut BTreeMap<String, Type>,
    ) {
        match expected {
            Type::TypeVar(name)
                if self.is_open_generic_member(name, receiver_type) && !actual.is_any() =>
            {
                bindings
                    .entry(name.clone())
                    .and_modify(|current| *current = current.join(actual))
                    .or_insert_with(|| actual.clone());
            }
            Type::Union(members) => {
                let fixed_match = members.iter().any(|member| {
                    !self.contains_open_generic_member(member, receiver_type)
                        && self.is_assignable(actual, member)
                });
                if !fixed_match {
                    for member in members {
                        if self.contains_open_generic_member(member, receiver_type) {
                            self.collect_generic_member_binding(
                                member,
                                actual,
                                receiver_type,
                                bindings,
                            );
                        }
                    }
                }
            }
            Type::Intersection(members) => {
                for member in members {
                    self.collect_generic_member_binding(member, actual, receiver_type, bindings);
                }
            }
            Type::Array(expected) => {
                if let Type::Array(actual) = actual {
                    self.collect_generic_member_binding(expected, actual, receiver_type, bindings);
                }
            }
            Type::Hash(expected_key, expected_value) => {
                if let Type::Hash(actual_key, actual_value) = actual {
                    self.collect_generic_member_binding(
                        expected_key,
                        actual_key,
                        receiver_type,
                        bindings,
                    );
                    self.collect_generic_member_binding(
                        expected_value,
                        actual_value,
                        receiver_type,
                        bindings,
                    );
                }
            }
            Type::Tuple(expected_elements) => {
                if let Type::Tuple(actual_elements) = actual {
                    for (expected, actual) in expected_elements.iter().zip(actual_elements) {
                        self.collect_generic_member_binding(
                            expected,
                            actual,
                            receiver_type,
                            bindings,
                        );
                    }
                }
            }
            Type::Proc(expected_parameters, expected_result) => {
                if let Type::Proc(actual_parameters, actual_result) = actual {
                    for (expected, actual) in expected_parameters.iter().zip(actual_parameters) {
                        self.collect_generic_member_binding(
                            expected,
                            actual,
                            receiver_type,
                            bindings,
                        );
                    }
                    self.collect_generic_member_binding(
                        expected_result,
                        actual_result,
                        receiver_type,
                        bindings,
                    );
                }
            }
            Type::Named(expected_name, expected_arguments) => {
                if let Type::Named(actual_name, actual_arguments) = actual {
                    if name_matches(expected_name, actual_name)
                        || name_matches(actual_name, expected_name)
                    {
                        for (expected, actual) in expected_arguments.iter().zip(actual_arguments) {
                            self.collect_generic_member_binding(
                                expected,
                                actual,
                                receiver_type,
                                bindings,
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn infer_generic_member_bindings(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
        receiver_type: Option<&Type>,
    ) -> BTreeMap<String, Type> {
        let mut bindings = BTreeMap::new();
        let positional_types = if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        for (actual, expected) in positional_types.iter().zip(&signature.params) {
            self.collect_generic_member_binding(expected, actual, receiver_type, &mut bindings);
        }
        if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
            for argument in &arguments.keyword_arguments {
                if let Some(expected) = signature.keywords.get(&argument.name) {
                    self.collect_generic_member_binding(
                        &expected.type_,
                        &argument.type_,
                        receiver_type,
                        &mut bindings,
                    );
                }
            }
        }
        bindings
    }

    fn substitute_generic_members(
        &self,
        type_: &Type,
        receiver_type: Option<&Type>,
        bindings: &BTreeMap<String, Type>,
    ) -> Type {
        match type_ {
            Type::TypeVar(name) => bindings
                .get(name)
                .cloned()
                .or_else(|| self.generic_member_binding(name, receiver_type))
                .unwrap_or_else(|| type_.clone()),
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| {
                        self.substitute_generic_members(argument, receiver_type, bindings)
                    })
                    .collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(self.substitute_generic_members(
                element,
                receiver_type,
                bindings,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(self.substitute_generic_members(key, receiver_type, bindings)),
                Box::new(self.substitute_generic_members(value, receiver_type, bindings)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        self.substitute_generic_members(element, receiver_type, bindings)
                    })
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| {
                        self.substitute_generic_members(parameter, receiver_type, bindings)
                    })
                    .collect(),
                Box::new(self.substitute_generic_members(result, receiver_type, bindings)),
            ),
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.substitute_generic_members(member, receiver_type, bindings)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| self.substitute_generic_members(member, receiver_type, bindings)),
            ),
            other => other.clone(),
        }
    }

    fn substitute_signature_type(
        &self,
        type_: &Type,
        receiver_type: Option<&Type>,
        bindings: &BTreeMap<String, Type>,
        type_parameters: &[String],
    ) -> Type {
        let names = type_parameters.iter().cloned().collect::<BTreeSet<_>>();
        let type_ = Self::substitute_instance_type(type_, receiver_type);
        let type_ = self.substitute_generic_members(&type_, receiver_type, bindings);
        Self::substitute_type_parameters(&type_, bindings, &names)
    }

    fn substitute_method_signature(
        &self,
        signature: &MethodSig,
        receiver_type: Option<&Type>,
    ) -> MethodSig {
        let bindings = BTreeMap::new();
        let mut result = signature.clone();
        result.params = signature
            .params
            .iter()
            .map(|type_| {
                self.substitute_signature_type(
                    type_,
                    receiver_type,
                    &bindings,
                    &signature.type_parameters,
                )
            })
            .collect();
        result.return_type = self.substitute_signature_type(
            &signature.return_type,
            receiver_type,
            &bindings,
            &signature.type_parameters,
        );
        result.keywords = signature
            .keywords
            .iter()
            .map(|(name, parameter)| {
                (
                    name.clone(),
                    signature::KeywordParam {
                        type_: self.substitute_signature_type(
                            &parameter.type_,
                            receiver_type,
                            &bindings,
                            &signature.type_parameters,
                        ),
                        required: parameter.required,
                    },
                )
            })
            .collect();
        result.block = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                receiver_type,
                &bindings,
                &signature.type_parameters,
            )
        });
        result
    }

    fn looks_like_class_name(name: &str) -> bool {
        let tail = name.rsplit_once("::").map_or(name, |(_, tail)| tail);
        tail.chars()
            .next()
            .is_some_and(|character| character.is_ascii_uppercase())
            && tail.chars().any(|character| character.is_ascii_lowercase())
    }

    fn record_inferred_return(&mut self, key: MethodKey, actual: Type, terminates: bool) {
        match self.pending_returns.entry(key) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert((actual, terminates));
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                let (current, current_terminates) = entry.get_mut();
                *current = current.join(&actual);
                *current_terminates &= terminates;
            }
        }
    }

    fn commit_inferred_returns(&mut self) {
        let pending_returns = std::mem::take(&mut self.pending_returns);
        for (key, (return_type, return_terminates)) in pending_returns {
            if let Some(state) = self.methods.get_mut(&key) {
                if !state.explicit {
                    state.return_type = Some(return_type);
                    state.return_terminates = return_terminates;
                }
            }
        }
    }

    fn run<'node>(mut self, root: &Node<'node>) -> CheckResult {
        if self.config.debug {
            eprintln!("[typey] registering declarations");
        }
        self.register_methods(root);
        let parse_diagnostics = std::mem::take(&mut self.diagnostics);
        if self.config.debug {
            eprintln!(
                "[typey] registered {} methods, {} classes, and {} type aliases",
                self.methods.len(),
                self.classes.len(),
                self.type_aliases.len()
            );
        }

        // First solve summaries without emitting diagnostics or retaining
        // transient node types. This is the same shape as Spinel's analysis:
        // all definitions are registered, then the tables are refined until
        // one complete pass makes no change.
        self.report = false;
        self.seed_calls = true;
        self.filter_method_bodies = false;
        self.debug_phase = "seed";
        self.debug_round = 0;
        self.types.clear();
        self.debug_nodes = 0;
        if self.config.debug {
            eprintln!("[typey] seeding top-level call sites");
        }
        self.pending_returns.clear();
        self.collecting_returns = true;
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);
        self.collecting_returns = false;
        self.commit_inferred_returns();
        self.seed_calls = false;
        self.changed_methods.clear();
        self.changed_shared.clear();

        let mut pending_methods = self.methods.keys().cloned().collect::<BTreeSet<_>>();
        let mut round = 0;
        // The worklist is driven solely by actual summary changes. There is
        // no arbitrary round limit: once no method or shared value changes,
        // the pending set is empty and the analysis has reached its fixed
        // point.
        loop {
            if pending_methods.is_empty() {
                break;
            }

            round += 1;
            self.active_methods = pending_methods.clone();
            self.filter_method_bodies = true;
            self.changed_methods.clear();
            self.changed_shared.clear();
            self.debug_phase = "inference";
            self.debug_round = round;
            self.types.clear();
            self.debug_nodes = 0;
            if self.config.debug {
                eprintln!(
                    "[typey] worklist round {round}: evaluating {} scheduled methods",
                    pending_methods.len()
                );
            }
            // Return summaries are computed synchronously: every method body
            // reads the summaries committed by the previous round, and all
            // candidates from this round are committed together below. This
            // avoids source-order effects when a caller appears before its
            // callee or when conditional branches define the same method.
            let previous_methods = self.methods.clone();
            self.pending_returns.clear();
            self.collecting_returns = true;
            let mut environment = Environment::default();
            self.eval_node(root, &mut environment);
            self.collecting_returns = false;
            self.commit_inferred_returns();

            let changed_methods = self
                .methods
                .iter()
                .filter_map(|(method, state)| {
                    (previous_methods.get(method) != Some(state)).then_some(method.clone())
                })
                .collect::<BTreeSet<_>>();
            self.changed_methods = changed_methods.clone();
            let changed_shared = self.changed_shared.clone();
            let mut next_pending = BTreeSet::new();
            for method in &changed_methods {
                next_pending.insert(method.clone());
                if let Some(callers) = self.method_callers.get(method) {
                    next_pending.extend(callers.iter().cloned());
                }
            }
            for shared_key in &changed_shared {
                if let Some(readers) = self.shared_readers.get(shared_key) {
                    next_pending.extend(readers.iter().cloned());
                }
            }
            if self.config.debug {
                eprintln!(
                    "[typey] worklist round {round} complete: {} changed methods, {} changed shared keys, {} scheduled next",
                    changed_methods.len(),
                    changed_shared.len(),
                    next_pending.len()
                );
            }
            pending_methods = next_pending;
        }

        // Re-run once with settled summaries. This final pass is the only pass
        // that publishes diagnostics and per-node types to callers.
        self.report = true;
        self.diagnostics = parse_diagnostics;
        self.seed_calls = false;
        self.types.clear();
        self.filter_method_bodies = false;
        self.active_methods.clear();
        self.debug_phase = "final";
        self.debug_round = 0;
        self.debug_nodes = 0;
        if self.config.debug {
            eprintln!("[typey] final reporting pass");
        }
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);

        self.report_inference_gaps();
        self.diagnostics.sort_by(|left, right| {
            left.start
                .cmp(&right.start)
                .then_with(|| left.message.cmp(&right.message))
        });
        if self.config.debug {
            eprintln!(
                "[typey] complete: {} diagnostics, {} recorded types",
                self.diagnostics.len(),
                self.types.len()
            );
        }
        CheckResult {
            diagnostics: self.diagnostics,
            types: self.types,
        }
    }

    fn report_inference_gaps(&mut self) {
        if self.config.strictness == Strictness::Ignore && self.strictness_ranges.is_empty() {
            return;
        }

        let gaps = self
            .definitions
            .iter()
            .filter_map(|(offset, key)| {
                let strictness = self.strictness_at(*offset);
                if strictness == Strictness::Ignore {
                    return None;
                }
                let state = self.methods.get(key)?;
                if state.explicit {
                    return None;
                }
                let unresolved_parameter = state
                    .params
                    .iter()
                    .any(|type_| type_.as_ref().map_or(true, Type::is_any));
                let unresolved_keyword = state
                    .keywords
                    .values()
                    .any(|type_| type_.as_ref().map_or(true, Type::is_any));
                let unresolved_return = state.return_type.as_ref().map_or(true, Type::is_any);
                (unresolved_parameter || unresolved_keyword || unresolved_return)
                    .then_some((*offset, key.clone()))
            })
            .collect::<Vec<_>>();

        for (offset, key) in gaps {
            let name = key.owner.as_ref().map_or_else(
                || key.name.clone(),
                |owner| format!("{owner}::{}", key.name),
            );
            self.diagnostics.push(Diagnostic::error(
                self.source,
                format!(
                    "Method `{name}` has insufficient inferred type information for strict mode"
                ),
                offset,
                offset,
            ));
        }
    }

    fn strictness_at(&self, offset: usize) -> Strictness {
        let mut strictness = self.config.strictness;
        for (start, end, candidate) in &self.strictness_ranges {
            if offset < *start || offset >= *end {
                continue;
            }
            if strictness_rank(*candidate) > strictness_rank(strictness) {
                strictness = *candidate;
            }
        }
        strictness
    }

    fn register_methods<'node>(&mut self, root: &Node<'node>) {
        self.methods.clear();
        self.type_aliases = self.annotations.type_aliases.clone();
        let mut registrar = MethodRegistrar {
            source: self.source,
            methods: &mut self.methods,
            definitions: &mut self.definitions,
            parameter_shapes: &mut self.parameter_shapes,
            classes: &mut self.classes,
            aliases: &mut self.aliases,
            accessors: &mut self.accessors,
            attribute_annotations: &self.annotations.attribute_annotations,
            class_type_parameters: &self.annotations.class_type_parameters,
            type_aliases: &mut self.type_aliases,
            constants: &mut self.constants,
            class_stack: Vec::new(),
            singleton_stack: Vec::new(),
            method_depth: 0,
        };
        registrar.visit(root);
        self.normalize_class_graph();

        // Resolve annotation offsets through the same definition table used by
        // body evaluation. This makes signatures owner-aware and prevents a
        // method called `remove` (or `initialize`) in one file from changing a
        // same-named method elsewhere in a workspace.
        let mut source_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let mut rbi_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let mut builtin_rbi_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        for (offset, signatures) in &self.annotations.method_annotations {
            let Some(key) = self.definitions.get(offset) else {
                continue;
            };
            let signatures = signatures
                .iter()
                .map(|signature| {
                    let signature = self.parameter_shapes.get(offset).map_or_else(
                        || signature.clone(),
                        |shape| apply_parameter_shape(signature, shape),
                    );
                    self.resolve_signature_names(&signature, key.owner.as_deref())
                })
                .collect::<Vec<_>>();
            let target = if self
                .builtin_rbi_ranges
                .iter()
                .any(|(start, end)| *offset >= *start && *offset < *end)
            {
                &mut builtin_rbi_signatures
            } else if self
                .rbi_ranges
                .iter()
                .any(|(start, end)| *offset >= *start && *offset < *end)
            {
                &mut rbi_signatures
            } else {
                &mut source_signatures
            };
            target.entry(key.clone()).or_default().extend(signatures);
        }
        for (key, signatures) in source_signatures.into_iter().chain(rbi_signatures) {
            if let Some(state) = self.methods.get_mut(&key) {
                if !state.explicit {
                    *state = MethodState::explicit_overloads(&signatures);
                }
            }
        }
        for (key, signatures) in builtin_rbi_signatures {
            if let Some(state) = self.methods.get_mut(&key) {
                if !state.explicit {
                    *state = MethodState::explicit_overloads(&signatures);
                }
            }
        }
    }

    fn record<'node>(&mut self, node: &Node<'node>, type_: Type) -> Type {
        let (start, end) = prism::span(node);
        let untyped_origin = if type_.contains_any() {
            self.untyped_origins
                .get(&(start, end))
                .copied()
                .or_else(|| {
                    let direct_unsafe = node.as_call_node().is_some_and(|call| {
                        prism::constant_name(call.name()) == "unsafe"
                            && call.receiver().is_some_and(|receiver| {
                                self.constant_reference_name(&receiver)
                                    .is_some_and(|name| name.trim_start_matches("::") == "T")
                            })
                    });
                    if direct_unsafe {
                        Some(UntypedOrigin::Unsafe)
                    } else {
                        Some(UntypedOrigin::Propagated)
                    }
                })
        } else {
            None
        };
        self.types.push(InferredType {
            start,
            end,
            type_: type_.clone(),
            untyped_origin,
            is_send: Self::is_send_node(node),
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

    fn eval_compound_assignment<'node>(
        &mut self,
        receiver: Type,
        operator: &str,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let value_result = self.eval_node(value_node, environment);
        let Some(value_type) = value_result.normal_type.clone() else {
            return value_result;
        };
        let site = CallSite {
            argument_nodes: std::slice::from_ref(value_node),
            argument_types: std::slice::from_ref(&value_type),
            block: None,
        };
        let result_type = self.eval_method_call(&receiver, operator, &site, environment);
        Eval::from_parts(Some(result_type), value_result.abrupt, value_result.flow)
    }

    fn eval_call_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        receiver_node: Option<Node<'node>>,
        read_name: &str,
        write_name: &str,
        value_node: Node<'node>,
        kind: CallAssignmentKind,
        environment: &mut Environment,
    ) -> Eval {
        let receiver_result = if let Some(receiver) = receiver_node.as_ref() {
            self.eval_node(receiver, environment)
        } else {
            Eval::value(environment.self_type.clone())
        };
        let receiver_type = receiver_result.normal_type.clone().unwrap_or(Type::Never);
        let getter_site = CallSite {
            argument_nodes: &[],
            argument_types: &[],
            block: None,
        };
        let current = self.eval_method_call(&receiver_type, read_name, &getter_site, environment);
        let value_result = match kind {
            CallAssignmentKind::Operator(operator) => {
                self.eval_compound_assignment(current, &operator, &value_node, environment)
            }
            CallAssignmentKind::And => self.eval_and_assignment(current, &value_node, environment),
            CallAssignmentKind::Or => self.eval_or_assignment(current, &value_node, environment),
        };
        if let Some(value_type) = value_result.normal_type.as_ref() {
            let setter_site = CallSite {
                argument_nodes: std::slice::from_ref(&value_node),
                argument_types: std::slice::from_ref(value_type),
                block: None,
            };
            let _ = self.eval_method_call(&receiver_type, write_name, &setter_site, environment);
        }
        let normal_type = receiver_result
            .normal_type
            .is_some()
            .then_some(value_result.normal_type.clone())
            .flatten();
        let mut result = Eval::from_parts(
            normal_type,
            receiver_result.abrupt.join(&value_result.abrupt),
            receiver_result.flow.union(value_result.flow),
        );
        let type_ = self.apply_inline_assertion(node, result.type_.clone());
        result.type_ = self.record(node, type_);
        result
    }

    fn eval_and_assignment<'node>(
        &mut self,
        current: Type,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let truthy = current.truthy_part();
        let mut right_environment = environment.clone();
        let right = if truthy.is_never() {
            Eval::value(Type::Never)
        } else {
            self.eval_node(value_node, &mut right_environment)
        };
        if !truthy.is_never() {
            *environment = environment.join(&right_environment);
        }
        let normal_type = Type::union([
            current.falsy_part(),
            right.normal_type.clone().unwrap_or(Type::Never),
        ]);
        let normal_type = (!normal_type.is_never()).then_some(normal_type);
        let abrupt = if truthy.is_never() {
            OutcomeTypes::default()
        } else {
            right.abrupt
        };
        let flow = if normal_type.is_some() {
            Flow::normal().union(abrupt.flow())
        } else {
            abrupt.flow()
        };
        Eval::from_parts(normal_type, abrupt, flow)
    }

    fn eval_or_assignment<'node>(
        &mut self,
        current: Type,
        value_node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let falsy = current.falsy_part();
        let mut right_environment = environment.clone();
        let right = if falsy.is_never() {
            Eval::value(Type::Never)
        } else {
            self.eval_node(value_node, &mut right_environment)
        };
        if !falsy.is_never() {
            *environment = environment.join(&right_environment);
        }
        let normal_type = Type::union([
            current.truthy_part(),
            right.normal_type.clone().unwrap_or(Type::Never),
        ]);
        let normal_type = (!normal_type.is_never()).then_some(normal_type);
        let abrupt = if falsy.is_never() {
            OutcomeTypes::default()
        } else {
            right.abrupt
        };
        let flow = if normal_type.is_some() {
            Flow::normal().union(abrupt.flow())
        } else {
            abrupt.flow()
        };
        Eval::from_parts(normal_type, abrupt, flow)
    }

    fn eval_index_access<'node>(
        &mut self,
        receiver_node: Option<Node<'node>>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        environment: &mut Environment,
    ) -> IndexAccess<'node> {
        let receiver_result = receiver_node.as_ref().map_or_else(
            || Eval::value(Type::Object),
            |receiver| self.eval_node(receiver, environment),
        );
        let argument_nodes = arguments
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        let evaluated = self.evaluate_call_arguments(argument_nodes, environment);
        let receiver_type = receiver_result.normal_type.clone().unwrap_or(Type::Never);
        IndexAccess {
            receiver_type,
            arguments: evaluated.arguments,
            abrupt: receiver_result.abrupt.join(&evaluated.abrupt),
            abrupt_flow: receiver_result
                .flow
                .without(FlowKind::Normal)
                .union(evaluated.abrupt_flow),
            all_normal: receiver_result.normal_type.is_some() && evaluated.all_normal,
        }
    }

    fn eval_index_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        receiver_node: Option<Node<'node>>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        value_node: Node<'node>,
        kind: IndexAssignmentKind,
        environment: &mut Environment,
    ) -> Eval {
        let access = self.eval_index_access(receiver_node, arguments, environment);
        let site = CallSite {
            argument_nodes: &access.arguments.argument_nodes,
            argument_types: &access.arguments.argument_types,
            block: None,
        };
        let current = self.eval_method_call(&access.receiver_type, "[]", &site, environment);
        let value_result = match kind {
            IndexAssignmentKind::Operator(operator) => self.eval_compound_assignment(
                current.without(&Type::Nil),
                &operator,
                &value_node,
                environment,
            ),
            IndexAssignmentKind::And => self.eval_and_assignment(current, &value_node, environment),
            IndexAssignmentKind::Or => self.eval_or_assignment(current, &value_node, environment),
        };
        let normal_type = if access.all_normal {
            value_result.normal_type
        } else {
            None
        };
        let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
        let abrupt = access.abrupt.join(&value_result.abrupt);
        let flow = access
            .abrupt_flow
            .union(value_result.flow.without(FlowKind::Normal));
        let flow = if normal_type.is_some() {
            Flow::normal().union(flow)
        } else {
            flow
        };
        let mut result = Eval::from_parts(normal_type, abrupt, flow);
        result.type_ = self.record(node, result.type_.clone());
        result
    }

    fn eval_node<'node>(&mut self, node: &Node<'node>, environment: &mut Environment) -> Eval {
        if self.config.debug {
            self.debug_nodes += 1;
            if self.debug_nodes.is_multiple_of(DEBUG_NODE_INTERVAL) {
                let (start, _) = prism::span(node);
                if self.debug_round == 0 {
                    eprintln!(
                        "[typey] {} pass: visited {} nodes (source offset {})",
                        self.debug_phase, self.debug_nodes, start
                    );
                } else {
                    eprintln!(
                        "[typey] fixpoint round {} {} pass: visited {} nodes (source offset {})",
                        self.debug_round, self.debug_phase, self.debug_nodes, start
                    );
                }
            }
        }
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
            if self.seed_calls || self.is_rbi_definition(node) {
                return Eval::value(Type::Nil);
            }
            let class_name = self.scoped_constant_name(
                environment,
                &self
                    .constant_reference_name(&class.constant_path())
                    .unwrap_or_else(|| prism::text(self.source, &class.constant_path())),
            );
            if let Some(body) = class.body() {
                let mut class_environment = environment.clone();
                class_environment.self_type = Self::class_object_type(&class_name);
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
            if self.seed_calls || self.is_rbi_definition(node) {
                return Eval::value(Type::Nil);
            }
            let module_name = self.scoped_constant_name(
                environment,
                &self
                    .constant_reference_name(&module.constant_path())
                    .unwrap_or_else(|| prism::text(self.source, &module.constant_path())),
            );
            if let Some(body) = module.body() {
                let mut module_environment = environment.clone();
                module_environment.self_type = Self::class_object_type(&module_name);
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
            if self.seed_calls || self.is_rbi_definition(node) {
                return Eval::value(Type::Nil);
            }
            let expression = singleton.expression();
            let expression_type = self.eval_node(&expression, environment).type_;
            let owner = match &expression_type {
                Type::Named(owner, arguments) if name_matches(owner, "Class") => arguments
                    .first()
                    .and_then(Self::named_type_name)
                    .or_else(|| self.constant_reference_name(&expression)),
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
        if let Some(multi) = node.as_multi_write_node() {
            let mut result = self.eval_node(&multi.value(), environment);
            if let Some(type_) = result.normal_type.clone() {
                let lefts = multi.lefts().into_iter().collect::<Vec<_>>();
                let rights = multi.rights().into_iter().collect::<Vec<_>>();
                let known_length = multi
                    .value()
                    .as_array_node()
                    .map(|array| array.elements().len());
                for (index, target) in lefts.iter().enumerate() {
                    self.bind_for_target(
                        target,
                        self.multi_assignment_element_type(&type_, index, known_length),
                        environment,
                    );
                }
                if let Some(rest) = multi.rest() {
                    self.bind_for_target(
                        &rest,
                        Type::union([
                            Type::Nil,
                            Type::Array(Box::new(self.array_element_type(&type_))),
                        ]),
                        environment,
                    );
                }
                let right_start = known_length
                    .map(|length| lefts.len().max(length.saturating_sub(rights.len())))
                    .unwrap_or(0);
                for (index, target) in rights.iter().enumerate() {
                    self.bind_for_target(
                        target,
                        self.multi_assignment_element_type(
                            &type_,
                            right_start + index,
                            known_length,
                        ),
                        environment,
                    );
                }
            }
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_operator_write_node() {
            let name = prism::constant_name(write.name());
            let current = self.constant_type(environment, &name);
            let value_node = write.value();
            let operator = prism::constant_name(write.binary_operator());
            let result =
                self.eval_compound_assignment(current, &operator, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_constant(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_and_write_node() {
            let name = prism::constant_name(write.name());
            let current = self.constant_type(environment, &name);
            let value_node = write.value();
            let result = self.eval_and_assignment(current, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_constant(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_or_write_node() {
            let name = prism::constant_name(write.name());
            let current = self.constant_type(environment, &name);
            let value_node = write.value();
            let result = self.eval_or_assignment(current, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_constant(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_write_node() {
            let value = write.value();
            let actual = Self::normal_type(self.eval_node(&value, environment));
            let name = prism::constant_name(write.name());
            let actual = self
                .struct_subclass_type(environment, &value, &name)
                .unwrap_or(actual);
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_constant(environment, name, &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_constant_path_operator_write_node() {
            let name = self.constant_path_name(&write.target());
            let current = self.constant_type(environment, &name);
            let value_node = write.value();
            let operator = prism::constant_name(write.binary_operator());
            let result =
                self.eval_compound_assignment(current, &operator, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_constant(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_path_and_write_node() {
            let name = self.constant_path_name(&write.target());
            let current = self.constant_type(environment, &name);
            let value_node = write.value();
            let result = self.eval_and_assignment(current, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_constant(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_path_or_write_node() {
            let name = self.constant_path_name(&write.target());
            let current = self.constant_type(environment, &name);
            let value_node = write.value();
            let result = self.eval_or_assignment(current, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_constant(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_constant_path_write_node() {
            let value = write.value();
            let actual = Self::normal_type(self.eval_node(&value, environment));
            let name = self.constant_path_name(&write.target());
            let actual = self
                .struct_subclass_type(environment, &value, &name)
                .unwrap_or(actual);
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_constant(environment, name, &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_class_variable_write_node() {
            let actual = Self::normal_type(self.eval_node(&write.value(), environment));
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_class_var(environment, prism::constant_name(write.name()), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_class_variable_operator_write_node() {
            let name = prism::constant_name(write.name());
            let value_node = write.value();
            let operator = prism::constant_name(write.binary_operator());
            let current = self.class_var_type(environment, &name);
            let result =
                self.eval_compound_assignment(current, &operator, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_class_var(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_class_variable_and_write_node() {
            let name = prism::constant_name(write.name());
            let value_node = write.value();
            let current = self.class_var_type(environment, &name);
            let result = self.eval_and_assignment(current, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_class_var(environment, name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_class_variable_or_write_node() {
            let current = self.class_var_type(environment, &prism::constant_name(write.name()));
            let previous = self.defer_inline_assertions;
            self.defer_inline_assertions = true;
            let right = Self::normal_type(self.eval_node(&write.value(), environment));
            self.defer_inline_assertions = previous;
            let actual = current.truthy_part().join(&right);
            let declared = self.apply_inline_assertion(node, actual);
            self.observe_class_var(environment, prism::constant_name(write.name()), &declared);
            let type_ = if right.without(&Type::Nil) == right {
                declared.without(&Type::Nil)
            } else {
                declared
            };
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_class_variable_read_node() {
            let actual = self.class_var_type(environment, &prism::constant_name(read.name()));
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_global_variable_write_node() {
            let actual = Self::normal_type(self.eval_node(&write.value(), environment));
            let type_ = self.apply_inline_assertion(node, actual);
            self.observe_global(prism::constant_name(write.name()), &type_);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_global_variable_operator_write_node() {
            let name = prism::constant_name(write.name());
            self.record_shared_read(SharedKey::Global(name.clone()), environment);
            let value_node = write.value();
            let operator = prism::constant_name(write.binary_operator());
            let result = self.eval_compound_assignment(
                self.globals.get(&name).cloned().unwrap_or(Type::Any),
                &operator,
                &value_node,
                environment,
            );
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_global(name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_global_variable_and_write_node() {
            let name = prism::constant_name(write.name());
            self.record_shared_read(SharedKey::Global(name.clone()), environment);
            let value_node = write.value();
            let result = self.eval_and_assignment(
                self.globals.get(&name).cloned().unwrap_or(Type::Any),
                &value_node,
                environment,
            );
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_global(name, type_);
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_global_variable_or_write_node() {
            let name = prism::constant_name(write.name());
            let current = self.globals.get(&name).cloned().unwrap_or(Type::Any);
            let previous = self.defer_inline_assertions;
            self.defer_inline_assertions = true;
            let right = Self::normal_type(self.eval_node(&write.value(), environment));
            self.defer_inline_assertions = previous;
            let actual = current.truthy_part().join(&right);
            let declared = self.apply_inline_assertion(node, actual);
            self.observe_global(name, &declared);
            let type_ = if right.without(&Type::Nil) == right {
                declared.without(&Type::Nil)
            } else {
                declared
            };
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_global_variable_read_node() {
            let name = prism::constant_name(read.name());
            self.record_shared_read(SharedKey::Global(name.clone()), environment);
            let actual = self.globals.get(&name).cloned().unwrap_or(Type::Any);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_instance_variable_write_node() {
            let value_node = write.value();
            let actual = Self::normal_type(self.eval_node(&value_node, environment));
            let name = prism::constant_name(write.name());
            let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
            let type_ = self.preserve_typed_empty_array_ivar(
                environment,
                &name,
                &value_node,
                type_,
            );
            self.observe_ivar(environment, name.clone(), &type_);
            environment.bind(ivar_refinement_key(&name), type_.clone());
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_instance_variable_operator_write_node() {
            let name = prism::constant_name(write.name());
            let value_node = write.value();
            let operator = prism::constant_name(write.binary_operator());
            let current = self.ivar_type(environment, &name);
            let result =
                self.eval_compound_assignment(current, &operator, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type
                .map(|type_| self.apply_inline_assertion_in_environment(node, type_, environment));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_ivar(environment, name.clone(), type_);
                environment.bind(ivar_refinement_key(&name), type_.clone());
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_instance_variable_and_write_node() {
            let name = prism::constant_name(write.name());
            let value_node = write.value();
            let current = self.ivar_type(environment, &name);
            let result = self.eval_and_assignment(current, &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type
                .map(|type_| self.apply_inline_assertion_in_environment(node, type_, environment));
            if let Some(type_) = normal_type.as_ref() {
                self.observe_ivar(environment, name.clone(), type_);
                environment.bind(ivar_refinement_key(&name), type_.clone());
            }
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_instance_variable_or_write_node() {
            let name = prism::constant_name(write.name());
            let current = self.ivar_type(environment, &name);
            let previous = self.defer_inline_assertions;
            self.defer_inline_assertions = true;
            let right = Self::normal_type(self.eval_node(&write.value(), environment));
            self.defer_inline_assertions = previous;
            let actual = current.truthy_part().join(&right);
            let declared = self.apply_inline_assertion_in_environment(node, actual, environment);
            let type_ = if right.without(&Type::Nil) == right {
                declared.without(&Type::Nil)
            } else {
                declared.clone()
            };
            self.observe_ivar(environment, name.clone(), &declared);
            environment.bind(ivar_refinement_key(&name), type_.clone());
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_instance_variable_read_node() {
            let name = prism::constant_name(read.name());
            let actual = self.ivar_type(environment, &name);
            let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_local_variable_write_node() {
            let value_node = write.value();
            let actual = Self::normal_type(self.eval_node(&value_node, environment));
            let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
            environment.bind(prism::constant_name(write.name()), type_.clone());
            return Eval::value(self.record(node, type_));
        }
        if let Some(write) = node.as_local_variable_operator_write_node() {
            let name = prism::constant_name(write.name());
            let value_node = write.value();
            let operator = prism::constant_name(write.binary_operator());
            let result = self.eval_compound_assignment(
                environment.get(&name),
                &operator,
                &value_node,
                environment,
            );
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| {
                let type_ = self.apply_inline_assertion_in_environment(node, type_, environment);
                environment.bind(name.clone(), type_.clone());
                type_
            });
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_local_variable_and_write_node() {
            let name = prism::constant_name(write.name());
            let value_node = write.value();
            let result = self.eval_and_assignment(environment.get(&name), &value_node, environment);
            let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
            let normal_type = normal_type.map(|type_| {
                let type_ = self.apply_inline_assertion_in_environment(node, type_, environment);
                environment.bind(name, type_.clone());
                type_
            });
            let mut result = Eval::from_parts(normal_type, abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if let Some(write) = node.as_local_variable_or_write_node() {
            let name = prism::constant_name(write.name());
            let current = environment.get(&name);
            let previous = self.defer_inline_assertions;
            self.defer_inline_assertions = true;
            let right = Self::normal_type(self.eval_node(&write.value(), environment));
            self.defer_inline_assertions = previous;
            let actual = current.truthy_part().join(&right);
            let declared = self.apply_inline_assertion_in_environment(node, actual, environment);
            environment.bind(
                name,
                if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared.clone()
                },
            );
            let type_ = if right.without(&Type::Nil) == right {
                declared.without(&Type::Nil)
            } else {
                declared
            };
            return Eval::value(self.record(node, type_));
        }
        if let Some(read) = node.as_local_variable_read_node() {
            let actual = environment.get(&prism::constant_name(read.name()));
            let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
            return Eval::value(self.record(node, type_));
        }
        if node.as_it_local_variable_read_node().is_some() {
            let type_ = self.apply_inline_assertion(node, environment.get("it"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(numbered) = node.as_numbered_reference_read_node() {
            let type_ = self
                .apply_inline_assertion(node, environment.get(&format!("_{}", numbered.number())));
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
        if node.as_defined_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::union([Type::Nil, Type::String]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(range) = node.as_range_node() {
            let left_type = range
                .left()
                .map_or(Type::Nil, |left| self.eval_node(&left, environment).type_);
            let right_type = range
                .right()
                .map_or(Type::Nil, |right| self.eval_node(&right, environment).type_);
            let type_ = self.apply_inline_assertion(
                node,
                Type::Named("Range".to_owned(), vec![left_type, right_type]),
            );
            return Eval::value(self.record(node, type_));
        }
        if node.as_regular_expression_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::named("Regexp"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(regexp) = node.as_interpolated_regular_expression_node() {
            for part in &regexp.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::named("Regexp"));
            return Eval::value(self.record(node, type_));
        }
        if node.as_source_file_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if node.as_source_line_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Integer);
            return Eval::value(self.record(node, type_));
        }
        if node.as_source_encoding_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::named("Encoding"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(flip_flop) = node.as_flip_flop_node() {
            if let Some(left) = flip_flop.left() {
                self.eval_node(&left, environment);
            }
            if let Some(right) = flip_flop.right() {
                self.eval_node(&right, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::bool());
            return Eval::value(self.record(node, type_));
        }
        if node.as_match_last_line_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::union([Type::Nil, Type::Integer]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(match_last_line) = node.as_interpolated_match_last_line_node() {
            for part in &match_last_line.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::union([Type::Nil, Type::Integer]));
            return Eval::value(self.record(node, type_));
        }
        if let Some(imaginary) = node.as_imaginary_node() {
            self.eval_node(&imaginary.numeric(), environment);
            let type_ = self.apply_inline_assertion(node, Type::named("Complex"));
            return Eval::value(self.record(node, type_));
        }
        if node.as_rational_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::named("Rational"));
            return Eval::value(self.record(node, type_));
        }
        if let Some(symbol) = node.as_interpolated_symbol_node() {
            for part in &symbol.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::Symbol);
            return Eval::value(self.record(node, type_));
        }
        if node.as_x_string_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(xstring) = node.as_interpolated_x_string_node() {
            for part in &xstring.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::String);
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
        if node.as_string_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(string) = node.as_interpolated_string_node() {
            for part in &string.parts() {
                self.eval_node(&part, environment);
            }
            let type_ = self.apply_inline_assertion(node, Type::String);
            return Eval::value(self.record(node, type_));
        }
        if let Some(embedded) = node.as_embedded_statements_node() {
            if let Some(statements) = embedded.statements() {
                return self.eval_node(&statements.as_node(), environment);
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(embedded) = node.as_embedded_variable_node() {
            return self.eval_node(&embedded.variable(), environment);
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
            let signature = MethodState::inferred(lambda.parameters().and_then(|parameters| {
                parameters
                    .as_block_parameters_node()
                    .and_then(|parameters| parameters.parameters())
                    .or_else(|| parameters.as_parameters_node())
            }))
            .body_signature();
            let parameters = lambda.parameters().and_then(|parameters| {
                parameters
                    .as_block_parameters_node()
                    .and_then(|parameters| parameters.parameters())
                    .or_else(|| parameters.as_parameters_node())
            });
            let mut closure_environment = environment.clone();
            self.bind_parameters(parameters, Some(&signature), &mut closure_environment);
            let body_result = lambda
                .body()
                .map(|body| self.eval_node(&body, &mut closure_environment))
                .unwrap_or_else(|| Eval::value(Type::Nil));
            let return_type = body_result.method_return_type();
            let type_ = self.apply_inline_assertion_in_environment(
                node,
                Type::Proc(signature.params, Box::new(return_type)),
                environment,
            );
            return Eval::value(self.record(node, type_));
        }
        if let Some(array) = node.as_array_node() {
            let mut element_types = Vec::new();
            let mut fixed_length = true;
            let mut element = Type::Never;
            for child in &array.elements() {
                let child_type = self.eval_node(&child, environment).type_;
                let child_type = if child.as_splat_node().is_some() {
                    fixed_length = false;
                    self.array_element_type(&child_type)
                } else {
                    child_type
                };
                element_types.push(child_type.clone());
                element = element.join(&child_type);
            }
            let element = if element.is_never() {
                Type::Any
            } else {
                element
            };
            let inferred = if fixed_length
                && self.expected_return_type.as_ref().is_some_and(|expected| {
                    matches!(expected, Type::Tuple(elements) if elements.len() == element_types.len())
                })
            {
                Type::Tuple(element_types)
            } else {
                Type::Array(Box::new(element))
            };
            let type_ = self.apply_inline_assertion_in_environment(node, inferred, environment);
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
                } else if let Some(splat) = child.as_assoc_splat_node() {
                    if let Some(expression) = splat.value() {
                        match self.eval_node(&expression, environment).type_ {
                            Type::Hash(splat_key, splat_value) => {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                            }
                            Type::Any => {
                                key = Type::Any;
                                value = Type::Any;
                            }
                            _ => {}
                        }
                    }
                } else {
                    self.eval_node(&child, environment);
                }
            }
            let key = if key.is_never() { Type::Any } else { key };
            let value = if value.is_never() { Type::Any } else { value };
            let type_ = self.apply_inline_assertion_in_environment(
                node,
                Type::Hash(Box::new(key), Box::new(value)),
                environment,
            );
            return Eval::value(self.record(node, type_));
        }
        if let Some(keyword_hash) = node.as_keyword_hash_node() {
            let mut key = Type::Never;
            let mut value = Type::Never;
            for child in &keyword_hash.elements() {
                if let Some(assoc) = child.as_assoc_node() {
                    key = key.join(&self.eval_node(&assoc.key(), environment).type_);
                    value = value.join(&self.eval_node(&assoc.value(), environment).type_);
                } else if let Some(splat) = child.as_assoc_splat_node() {
                    if let Some(expression) = splat.value() {
                        match self.eval_node(&expression, environment).type_ {
                            Type::Hash(splat_key, splat_value) => {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                            }
                            Type::Any => {
                                key = Type::Any;
                                value = Type::Any;
                            }
                            _ => {}
                        }
                    }
                }
            }
            let key = if key.is_never() { Type::Any } else { key };
            let value = if value.is_never() { Type::Any } else { value };
            let type_ = self.apply_inline_assertion_in_environment(
                node,
                Type::Hash(Box::new(key), Box::new(value)),
                environment,
            );
            return Eval::value(self.record(node, type_));
        }
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                let result = self.eval_node(&body, environment);
                let type_ = self.apply_inline_assertion_in_environment(
                    node,
                    result.type_.clone(),
                    environment,
                );
                return Eval {
                    type_: self.record(node, type_),
                    ..result
                };
            }
            let type_ = self.apply_inline_assertion_in_environment(node, Type::Nil, environment);
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
        if let Some(yield_node) = node.as_yield_node() {
            let argument_nodes = yield_node
                .arguments()
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            let evaluated = self.evaluate_call_arguments(argument_nodes, environment);
            let arguments = evaluated.arguments;
            let argument_types = arguments.argument_types.clone();
            let method_key = environment.method_key.clone();
            if let Some(key) = method_key.as_ref() {
                if let Some(state) = self.methods.get_mut(key) {
                    if state.observe_yield_arguments(&argument_types) {
                        self.changed_methods.insert(key.clone());
                    }
                }
            }
            let block_return_type = method_key
                .as_ref()
                .and_then(|key| self.methods.get(key))
                .and_then(|state| state.block_return_type.clone())
                .unwrap_or(Type::Any);
            let normal_type = evaluated.all_normal.then_some(block_return_type);
            let flow = evaluated.abrupt_flow.union(
                normal_type
                    .as_ref()
                    .map_or(Flow::empty(), |_| Flow::normal()),
            );
            let mut result = Eval::from_parts(normal_type, evaluated.abrupt, flow);
            result.type_ = self.record(node, result.type_.clone());
            return result;
        }
        if node.as_retry_node().is_some() {
            let type_ = self.apply_inline_assertion(node, Type::Never);
            return Eval::retried(self.record(node, type_));
        }
        if let Some(super_node) = node.as_super_node() {
            let block = super_node.block();
            let actual = self.eval_super(
                node,
                super_node.arguments(),
                None,
                block.as_ref(),
                environment,
            );
            let type_ = self.apply_inline_assertion(node, actual);
            let type_ = self.record(node, type_);
            if self.super_terminates(environment) {
                return Eval::raised(type_);
            } else {
                return Eval::value(type_);
            }
        }
        if let Some(super_node) = node.as_forwarding_super_node() {
            let block = super_node.block().map(|block| block.as_node());
            let actual =
                self.eval_super(node, None, Some(&super_node), block.as_ref(), environment);
            let type_ = self.apply_inline_assertion(node, actual);
            let type_ = self.record(node, type_);
            if self.super_terminates(environment) {
                return Eval::raised(type_);
            } else {
                return Eval::value(type_);
            }
        }
        if let Some(write) = node.as_index_operator_write_node() {
            let operator = prism::constant_name(write.binary_operator());
            return self.eval_index_assignment(
                node,
                write.receiver(),
                write.arguments(),
                write.value(),
                IndexAssignmentKind::Operator(operator),
                environment,
            );
        }
        if let Some(write) = node.as_index_and_write_node() {
            return self.eval_index_assignment(
                node,
                write.receiver(),
                write.arguments(),
                write.value(),
                IndexAssignmentKind::And,
                environment,
            );
        }
        if let Some(write) = node.as_index_or_write_node() {
            return self.eval_index_assignment(
                node,
                write.receiver(),
                write.arguments(),
                write.value(),
                IndexAssignmentKind::Or,
                environment,
            );
        }
        if let Some(write) = node.as_call_operator_write_node() {
            return self.eval_call_assignment(
                node,
                write.receiver(),
                &prism::constant_name(write.read_name()),
                &prism::constant_name(write.write_name()),
                write.value(),
                CallAssignmentKind::Operator(prism::constant_name(write.binary_operator())),
                environment,
            );
        }
        if let Some(write) = node.as_call_and_write_node() {
            return self.eval_call_assignment(
                node,
                write.receiver(),
                &prism::constant_name(write.read_name()),
                &prism::constant_name(write.write_name()),
                write.value(),
                CallAssignmentKind::And,
                environment,
            );
        }
        if let Some(write) = node.as_call_or_write_node() {
            return self.eval_call_assignment(
                node,
                write.receiver(),
                &prism::constant_name(write.read_name()),
                &prism::constant_name(write.write_name()),
                write.value(),
                CallAssignmentKind::Or,
                environment,
            );
        }
        if let Some(call) = node.as_call_node() {
            let mut result = self.eval_call(node, &call, environment);
            let type_ =
                self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
            if result.normal_type.is_some() {
                result.normal_type = Some(type_.clone());
            }
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(block) = node.as_block_node() {
            let block_type = self.eval_block(&block, &[], environment).type_;
            let type_ = self.apply_inline_assertion_in_environment(node, block_type, environment);
            let type_ = self.apply_inline_assertion_in_environment(node, type_, environment);
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
            let type_ =
                self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(until_node) = node.as_until_node() {
            let predicate = until_node.predicate();
            let statements = until_node.statements();
            let mut result = self.eval_loop(&predicate, statements.as_ref(), environment, false);
            let type_ =
                self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
            result.type_ = self.record(node, type_);
            return result;
        }
        if let Some(for_node) = node.as_for_node() {
            return self.eval_for(node, &for_node, environment);
        }

        let type_ = self.apply_inline_assertion_in_environment(node, Type::Any, environment);
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
                let evaluated = self.eval_node(&exception, &mut rescue_environment).type_;
                let exception_type_for_clause = if exception.as_splat_node().is_some() {
                    self.array_element_type(&evaluated)
                } else {
                    evaluated
                };
                let exception_type_for_clause =
                    Self::class_object_value_type(&exception_type_for_clause)
                        .unwrap_or(exception_type_for_clause);
                exception_type = exception_type.join(&exception_type_for_clause);
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
        let predicate_type = predicate
            .as_ref()
            .map(|predicate| self.eval_node(predicate, environment).type_);
        let base = environment.clone();
        let mut branch_environment: Option<Environment> = None;
        let mut result: Option<Eval> = None;
        let mut covered_type = Type::Never;
        let mut terminating_type = Type::Never;
        let mut all_conditions_are_type_tests = true;

        for condition in &case_node.conditions() {
            let Some(when_node) = condition.as_when_node() else {
                continue;
            };
            let mut when_environment = base.clone();
            let mut condition_type = Type::Never;
            let mut condition_is_type_test = true;
            for value in &when_node.conditions() {
                let is_type_test = Self::is_case_type_test(&value);
                all_conditions_are_type_tests &= is_type_test;
                condition_is_type_test &= is_type_test;
                let value_type = self.eval_node(&value, &mut when_environment).type_;
                let value_type = Self::class_object_value_type(&value_type).unwrap_or(value_type);
                condition_type = condition_type.join(&value_type);
            }
            covered_type = covered_type.join(&condition_type);
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target(predicate, &mut when_environment, &condition_type);
            }
            let when_result = if let Some(statements) = when_node.statements() {
                self.eval_statements(&statements, &mut when_environment)
            } else {
                Eval::value(Type::Nil)
            };
            if condition_is_type_test && !when_result.flow.contains(FlowKind::Normal) {
                terminating_type = terminating_type.join(&condition_type);
            }
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
        if !terminating_type.is_never() {
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target_excluding(
                    predicate,
                    &mut else_environment,
                    &terminating_type,
                );
            }
        }
        let else_result = if let Some(else_clause) = case_node.else_clause() {
            if let Some(statements) = else_clause.statements() {
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            // The unmatched path remains possible unless the predicate's
            // finite union is covered by the `when` conditions. Preserve its
            // narrowed environment for statements after the case, while
            // avoiding a spurious nil value for exhaustive class switches.
            let unmatched = predicate_type.as_ref().map(|candidate| {
                self.case_unmatched_type(candidate, &covered_type, all_conditions_are_type_tests)
            });
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target_without(
                    predicate,
                    &mut else_environment,
                    &covered_type,
                    all_conditions_are_type_tests,
                );
            }
            if unmatched.as_ref().is_some_and(Type::is_never) {
                Eval::from_parts(None, OutcomeTypes::default(), Flow::empty())
            } else {
                Eval::value(Type::Nil)
            }
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

    fn narrow_case_target_without<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        excluded: &Type,
        all_conditions_are_type_tests: bool,
    ) {
        if let Some(local) = predicate.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            let current = environment.get(&name);
            environment.bind(
                name,
                self.case_unmatched_type(&current, excluded, all_conditions_are_type_tests),
            );
        }
    }

    fn narrow_case_target_excluding<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        excluded: &Type,
    ) {
        if let Some(local) = predicate.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            let current = environment.get(&name);
            environment.bind(name, current.without(excluded));
        }
    }

    fn is_case_type_test(node: &Node<'_>) -> bool {
        node.as_constant_read_node().is_some()
            || node.as_constant_path_node().is_some()
            || node.as_true_node().is_some()
            || node.as_false_node().is_some()
            || node.as_nil_node().is_some()
    }

    fn case_unmatched_type(
        &self,
        candidate: &Type,
        covered: &Type,
        all_conditions_are_type_tests: bool,
    ) -> Type {
        if !all_conditions_are_type_tests {
            return candidate.clone();
        }
        match candidate {
            Type::Any => Type::Any,
            Type::Union(members) => Type::union(members.iter().filter_map(|member| {
                (!self.is_assignable(member, covered)).then_some(member.clone())
            })),
            candidate if self.is_assignable(candidate, covered) => Type::Never,
            candidate => candidate.clone(),
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
        let type_ = self.node_type(pattern, environment);
        Self::class_object_value_type(&type_).unwrap_or(type_)
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
        loop {
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
        loop {
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

    fn multi_assignment_element_type(
        &self,
        type_: &Type,
        index: usize,
        known_length: Option<usize>,
    ) -> Type {
        match type_ {
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.multi_assignment_element_type(member, index, known_length)),
            ),
            Type::Tuple(elements) => elements.get(index).cloned().unwrap_or(Type::Nil),
            Type::Array(element) => {
                if known_length.is_some_and(|length| index >= length) {
                    Type::Nil
                } else if known_length.is_some() {
                    element.as_ref().clone()
                } else {
                    Type::union([element.as_ref().clone(), Type::Nil])
                }
            }
            Type::Nil => Type::Nil,
            Type::Any => Type::Any,
            _ => Type::Any,
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
        if self.filter_method_bodies && !self.active_methods.contains(&key) {
            return Eval::value(Type::Nil);
        }
        self.begin_method_evaluation(&key);
        let state = self
            .methods
            .get(&key)
            .cloned()
            .unwrap_or_else(|| MethodState::inferred(definition.parameters()));
        let mut method_environment = Environment {
            self_type: key.owner.as_ref().map_or(Type::Object, |owner| {
                if key.singleton {
                    Self::class_object_type(owner)
                } else {
                    self.instance_self_type(owner)
                }
            }),
            method_key: Some(key.clone()),
            ..Environment::default()
        };
        let body_signature = self.substitute_method_signature(
            &state.body_signature(),
            Some(&method_environment.self_type),
        );
        self.bind_parameters(
            definition.parameters(),
            Some(&body_signature),
            &mut method_environment,
        );
        if let Some(parameters) = definition.parameters() {
            if let Some(block) = parameters.block() {
                if let Some(name) = block.name() {
                    method_environment.bind(
                        prism::constant_name(name),
                        Type::Proc(
                            state.block_parameters(),
                            Box::new(state.block_result_type()),
                        ),
                    );
                }
            }
        }

        let previous_expected_return = self.expected_return_type.take();
        self.expected_return_type = if state.explicit && !state.is_void {
            let signature = self.substitute_method_signature(
                &state.call_signature(),
                Some(&method_environment.self_type),
            );
            Some(signature.return_type)
        } else {
            None
        };
        let body_result = if let Some(body) = definition.body() {
            self.eval_node(&body, &mut method_environment)
        } else {
            Eval::value(Type::Nil)
        };
        self.expected_return_type = previous_expected_return;
        let inferred_return = body_result.method_return_type();
        if state.explicit && !state.is_void && !self.is_rbi_definition(node) {
            let expected = self.substitute_method_signature(
                &state.call_signature(),
                Some(&method_environment.self_type),
            );
            if !inferred_return.is_never()
                && !self.is_assignable(&inferred_return, &expected.return_type)
            {
                self.error(
                    node,
                    format!(
                        "Expected method `{name}` to return `{}`, but found `{}`",
                        expected.return_type, inferred_return
                    ),
                );
            }
        } else if self.collecting_returns {
            self.record_inferred_return(
                key,
                inferred_return,
                body_result.flow == Flow::abrupt(FlowKind::Raise),
            );
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
        block: Option<&Node<'node>>,
        environment: &mut Environment,
    ) -> Type {
        let Some(current) = environment.method_key.clone() else {
            return Type::Any;
        };
        let target = self.super_method_key(&current);
        let arguments = if forwarding.is_some() {
            let types = self
                .methods
                .get(&current)
                .map(|state| state.call_signature().params)
                .unwrap_or_default();
            let positional_types = types.clone();
            CallArguments {
                argument_nodes: Vec::new(),
                argument_types: types,
                argument_indices: Vec::new(),
                positional_indices: Vec::new(),
                positional_types,
                keyword_arguments: Vec::new(),
                has_keyword_splat: false,
                has_dynamic_positional_splat: false,
                dynamic_positional_splat_types: Vec::new(),
                has_dynamic_keyword_splat: false,
                has_unknown_positional_splat: false,
                has_unknown_keyword_splat: false,
                forwards_arguments: true,
            }
        } else {
            let argument_nodes = arguments
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            self.evaluate_call_arguments(argument_nodes, environment)
                .arguments
        };
        let Some(target) = target else {
            if let Some(block) = block {
                let _ = self.eval_block_node(block, &[Type::Any], environment);
            }
            return Type::Any;
        };
        self.record_method_dependency(&target, environment);
        let Some(signature) = self.observe_call(&target, &arguments, block.is_some()) else {
            if let Some(block) = block {
                let _ = self.eval_block_node(block, &[Type::Any], environment);
            }
            return Type::Any;
        };
        let receiver_type = environment.self_type.clone();
        let block_return_type = self.observe_block_call(
            &target,
            block,
            &signature,
            &arguments,
            Some(&receiver_type),
            environment,
        );
        self.invoke_signature(
            node,
            &target.name,
            &signature,
            &arguments,
            Some(&environment.self_type),
            block_return_type.as_ref(),
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
                self.eval_node(&optional.value(), environment);
                index += 1;
            }
        }
        if let Some(rest) = parameters
            .rest()
            .and_then(|node| node.as_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                let element_type = signature
                    .and_then(|signature| signature.params.get(index))
                    .cloned()
                    .unwrap_or(Type::Any);
                environment.bind(
                    prism::constant_name(name),
                    Type::Array(Box::new(element_type)),
                );
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
                self.bind_keyword_parameter(environment, required.name(), signature);
            } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                self.bind_keyword_parameter(environment, optional.name(), signature);
                self.eval_node(&optional.value(), environment);
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

    fn bind_keyword_parameter<'node>(
        &self,
        environment: &mut Environment,
        name: ruby_prism::ConstantId<'node>,
        signature: Option<&MethodSig>,
    ) {
        let name = prism::constant_name(name);
        let type_ = signature
            .and_then(|signature| signature.keywords.get(&name))
            .map_or(Type::Any, |parameter| parameter.type_.clone());
        environment.bind(name, type_);
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
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
        truthy: bool,
    ) {
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                self.narrow_from_predicate(&body, environment, truthy);
            }
            return;
        }
        if let Some(statements) = node.as_statements_node() {
            let body = statements.body();
            if let Some(last) = (&body).into_iter().last() {
                self.narrow_from_predicate(&last, environment, truthy);
            }
            return;
        }
        if let Some(and) = node.as_and_node() {
            if truthy {
                let left = and.left();
                self.narrow_from_predicate(&left, environment, true);
                let right = and.right();
                self.narrow_from_predicate(&right, environment, true);
            }
            return;
        }
        if let Some(or) = node.as_or_node() {
            if !truthy {
                let left = or.left();
                self.narrow_from_predicate(&left, environment, false);
                let right = or.right();
                self.narrow_from_predicate(&right, environment, false);
            }
            return;
        }
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
        if let Some(write) = node.as_local_variable_write_node() {
            let name = prism::constant_name(write.name());
            let current = environment.get(&name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(name, current.meet(&narrowed));
            return;
        }
        if let Some(instance_variable) = node.as_instance_variable_read_node() {
            let name = prism::constant_name(instance_variable.name());
            let current = self.ivar_type(environment, &name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(ivar_refinement_key(&name), current.meet(&narrowed));
            return;
        }
        if let Some(call) = node.as_call_node() {
            let name = prism::constant_name(call.name());
            let receiver = call.receiver();
            let arguments = call
                .arguments()
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            if name == "!" {
                if let Some(receiver) = receiver {
                    self.narrow_from_predicate(&receiver, environment, !truthy);
                }
                return;
            }
            if let Some(receiver) = receiver {
                if let Some(local) = receiver.as_local_variable_read_node() {
                    let local_name = prism::constant_name(local.name());
                    let current = environment.get(&local_name);
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
                } else if let Some(instance_variable) = receiver.as_instance_variable_read_node() {
                    let instance_variable_name = prism::constant_name(instance_variable.name());
                    let current = self.ivar_type(environment, &instance_variable_name);
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
                    environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                }
            }
        }
    }

    fn evaluate_call_arguments<'node>(
        &mut self,
        argument_nodes: Vec<Node<'node>>,
        environment: &mut Environment,
    ) -> CallArgumentEvaluation<'node> {
        let mut evaluated = CallArguments::default();
        let mut abrupt = OutcomeTypes::default();
        let mut abrupt_flow = Flow::empty();
        let mut all_normal = true;

        for (argument_index, argument) in argument_nodes.iter().enumerate() {
            if argument.as_forwarding_arguments_node().is_some() {
                evaluated.forwards_arguments = true;
                continue;
            }
            if let Some(keyword_hash) = argument.as_keyword_hash_node() {
                let mut key = Type::Never;
                let mut value = Type::Never;
                let mut keyword_arguments = Vec::new();
                let mut keyword_shape = true;
                let mut child_flow = Flow::normal();
                let mut child_abrupt = OutcomeTypes::default();

                for child in &keyword_hash.elements() {
                    if let Some(assoc) = child.as_assoc_node() {
                        let key_node = assoc.key();
                        let key_result = self.eval_node(&key_node, environment);
                        key = key.join(&key_result.type_);
                        child_abrupt = child_abrupt.join(&key_result.abrupt);
                        child_flow = child_flow.without(FlowKind::Normal).union(key_result.flow);

                        let value_node = assoc.value();
                        let value_result = self.eval_node(&value_node, environment);
                        value = value.join(&value_result.type_);
                        child_abrupt = child_abrupt.join(&value_result.abrupt);
                        child_flow = child_flow
                            .without(FlowKind::Normal)
                            .union(value_result.flow);

                        if let Some(symbol) = key_node.as_symbol_node() {
                            keyword_arguments.push(KeywordArgument {
                                name: String::from_utf8_lossy(symbol.unescaped()).into_owned(),
                                node: value_node,
                                type_: value_result.type_,
                            });
                        } else {
                            keyword_shape = false;
                        }
                    } else if let Some(splat) = child.as_assoc_splat_node() {
                        if let Some(expression) = splat.value() {
                            let result = self.eval_node(&expression, environment);
                            child_abrupt = child_abrupt.join(&result.abrupt);
                            child_flow = child_flow.without(FlowKind::Normal).union(result.flow);
                            let result_type = result.type_.clone();
                            if let Type::Hash(splat_key, splat_value) = result_type {
                                key = key.join(&splat_key);
                                value = value.join(&splat_value);
                                evaluated.has_dynamic_keyword_splat = true;
                            } else {
                                key = Type::Any;
                                value = Type::Any;
                                if result_type.is_any() {
                                    evaluated.has_unknown_keyword_splat = true;
                                } else {
                                    evaluated.has_dynamic_keyword_splat = true;
                                }
                            }
                        }
                        evaluated.has_keyword_splat = true;
                    } else {
                        keyword_shape = false;
                        let result = self.eval_node(&child, environment);
                        child_abrupt = child_abrupt.join(&result.abrupt);
                        child_flow = child_flow.without(FlowKind::Normal).union(result.flow);
                    }
                }

                if keyword_shape {
                    let key = if key.is_never() { Type::Any } else { key };
                    let value = if value.is_never() { Type::Any } else { value };
                    let type_ = self.apply_inline_assertion(
                        argument,
                        Type::Hash(Box::new(key), Box::new(value)),
                    );
                    let type_ = self.record(argument, type_);
                    evaluated.argument_types.push(type_);
                    evaluated.argument_indices.push(argument_index);
                    evaluated.keyword_arguments.extend(keyword_arguments);
                    abrupt = abrupt.join(&child_abrupt);
                    abrupt_flow = abrupt_flow.union(child_flow.without(FlowKind::Normal));
                    all_normal &= child_flow.contains(FlowKind::Normal);
                    continue;
                }
            }

            if let Some(splat) = argument.as_splat_node() {
                let Some(expression) = splat.expression() else {
                    evaluated.forwards_arguments = true;
                    continue;
                };
                let result = self.eval_splat_expression(&expression, environment);
                if let Type::Tuple(elements) = &result.type_ {
                    for type_ in elements {
                        evaluated.argument_types.push(type_.clone());
                        evaluated.argument_indices.push(argument_index);
                        evaluated.positional_types.push(type_.clone());
                        evaluated.positional_indices.push(argument_index);
                    }
                } else if result.type_.is_any() {
                    evaluated.has_unknown_positional_splat = true;
                } else {
                    evaluated.has_dynamic_positional_splat = true;
                    evaluated
                        .dynamic_positional_splat_types
                        .push(result.type_.clone());
                }
                abrupt = abrupt.join(&result.abrupt);
                abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
                all_normal &= result.flow.contains(FlowKind::Normal);
                continue;
            }

            let result = self.eval_node(argument, environment);
            evaluated.argument_types.push(result.type_.clone());
            evaluated.argument_indices.push(argument_index);
            evaluated.positional_types.push(result.type_);
            evaluated.positional_indices.push(argument_index);
            abrupt = abrupt.join(&result.abrupt);
            abrupt_flow = abrupt_flow.union(result.flow.without(FlowKind::Normal));
            all_normal &= result.flow.contains(FlowKind::Normal);
        }

        // Keyword hashes remain in the complete argument list for built-in
        // method models, but only their named entries participate in a
        // keyword-shaped signature.
        evaluated.argument_nodes = argument_nodes;
        CallArgumentEvaluation {
            arguments: evaluated,
            abrupt,
            abrupt_flow,
            all_normal,
        }
    }

    fn eval_splat_expression<'node>(
        &mut self,
        expression: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let previous_expected_return = self.expected_return_type.take();
        if let Some(array) = expression.as_array_node() {
            if array
                .elements()
                .iter()
                .all(|element| element.as_splat_node().is_none())
            {
                self.expected_return_type =
                    Some(Type::Tuple(vec![Type::Any; array.elements().len()]));
            }
        }
        let result = self.eval_node(expression, environment);
        self.expected_return_type = previous_expected_return;
        result
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
        let evaluated = self.evaluate_call_arguments(argument_nodes, environment);
        let arguments = evaluated.arguments;
        let argument_types = &arguments.argument_types;
        let mut abrupt = evaluated.abrupt;
        let mut abrupt_flow = evaluated.abrupt_flow;
        let mut all_normal = evaluated.all_normal;
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
        let block = call.block();
        let mut untyped_origin = None;
        let callee_type = if receiver_node.as_ref().is_some_and(|receiver| {
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
        } else if receiver_node.is_none()
            && matches!(name.as_str(), "lambda" | "proc")
            && call.block().is_some()
        {
            let (parameters, return_type) = call.block().as_ref().map_or_else(
                || (Vec::new(), Type::Any),
                |block| {
                    let signature = Self::inferred_block_signature(block);
                    let return_type = self.eval_block_node(block, &signature.params, environment);
                    (signature.params, return_type)
                },
            );
            Type::Proc(parameters, Box::new(return_type))
        } else if receiver_node.is_none() {
            if name == "each"
                && Self::named_type_name(&environment.self_type)
                    .is_some_and(|owner| name_matches(&owner, "Enumerable"))
            {
                if let Some(block) = block.as_ref() {
                    let _ = self.eval_block_node(block, &[Type::Any], environment);
                }
            }
            let key = self.implicit_method_key(&name, environment);
            self.record_method_dependency(&key, environment);
            if let Some(signature) = self.observe_call(&key, &arguments, block.is_some()) {
                let declared = self
                    .resolve_method_key(&key)
                    .and_then(|resolved| self.methods.get(&resolved))
                    .is_some_and(|state| state.explicit);
                let receiver_type = environment.self_type.clone();
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
                        self.infer_initializer_call(node, &owner, &arguments, environment);
                        Type::named(owner)
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
                type_
            }
        } else {
            let site = CallSite {
                argument_nodes: &arguments.argument_nodes,
                argument_types,
                block: block.as_ref(),
            };
            let dispatch_receiver_type = if call.is_safe_navigation() {
                receiver_type.without(&Type::Nil)
            } else {
                receiver_type.clone()
            };
            let mut result = if matches!(
                dispatch_receiver_type,
                Type::Union(_) | Type::Intersection(_)
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
                self.record_method_dependency(&key, environment);
                let inferred_accessor = self
                    .resolve_method_key(&key)
                    .filter(|resolved| {
                        self.methods
                            .get(resolved)
                            .is_some_and(|state| !state.explicit)
                    })
                    .and_then(|resolved| {
                        self.accessors
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
                } else if let Some(signature) = self.observe_call(&key, &arguments, block.is_some())
                {
                    let declared = self
                        .resolve_method_key(&key)
                        .and_then(|resolved| self.methods.get(&resolved))
                        .is_some_and(|state| state.explicit);
                    let block_return_type = self.observe_block_call(
                        &key,
                        block.as_ref(),
                        &signature,
                        &arguments,
                        Some(&dispatch_receiver_type),
                        environment,
                    );
                    let type_ = self.invoke_signature(
                        node,
                        &name,
                        &signature,
                        &arguments,
                        Some(&dispatch_receiver_type),
                        block_return_type.as_ref(),
                    );
                    if type_.contains_any() {
                        untyped_origin = Some(if declared {
                            UntypedOrigin::DeclaredSignature
                        } else {
                            UntypedOrigin::InferredMethod
                        });
                    }
                    type_
                } else {
                    let type_ =
                        self.eval_method_call(&dispatch_receiver_type, &name, &site, environment);
                    if type_.contains_any() {
                        untyped_origin = Some(if dispatch_receiver_type.contains_any() {
                            UntypedOrigin::Propagated
                        } else {
                            UntypedOrigin::FallbackCall
                        });
                    }
                    type_
                }
            } else {
                let type_ =
                    self.eval_method_call(&dispatch_receiver_type, &name, &site, environment);
                if type_.contains_any() {
                    untyped_origin = Some(if dispatch_receiver_type.contains_any() {
                        UntypedOrigin::Propagated
                    } else {
                        UntypedOrigin::FallbackCall
                    });
                }
                type_
            };
            if name == "new"
                && receiver_node
                    .as_ref()
                    .is_some_and(|receiver| self.constant_reference_name(receiver).is_some())
            {
                if let Some(owner) = Self::class_object_owner(&receiver_type) {
                    self.infer_initializer_call(node, &owner, &arguments, environment);
                    result = Type::named(owner);
                }
            }
            if call.is_safe_navigation() && !receiver_type.is_any() {
                Type::union([Type::Nil, result])
            } else {
                result
            }
        };

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

    fn eval_polymorphic_receiver_call<'a, 'node>(
        &mut self,
        node: &Node<'node>,
        receiver_node: Option<&Node<'node>>,
        receiver_type: &Type,
        name: &str,
        arguments: &CallArguments<'node>,
        block: Option<&Node<'node>>,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> (Type, UntypedOrigin) {
        if let Type::Union(members) = receiver_type {
            let mut result = Type::Never;
            let mut fallback_origin = UntypedOrigin::FallbackCall;
            for member in members {
                let (member_type, member_origin) = self.eval_polymorphic_receiver_call(
                    node,
                    receiver_node,
                    member,
                    name,
                    arguments,
                    block,
                    site,
                    environment,
                );
                if member_type.contains_any() {
                    fallback_origin = member_origin;
                }
                result = result.join(&member_type);
            }
            return (
                if result.is_never() { Type::Any } else { result },
                fallback_origin,
            );
        }

        if let Type::Intersection(members) = receiver_type {
            for member in members {
                let Some(key) = self.receiver_method_key(receiver_node, member, name, environment)
                else {
                    continue;
                };
                if let Some((type_, declared)) = self.eval_resolved_receiver_call(
                    node,
                    name,
                    &key,
                    member,
                    arguments,
                    block,
                    environment,
                ) {
                    let origin = if declared {
                        UntypedOrigin::DeclaredSignature
                    } else {
                        UntypedOrigin::InferredMethod
                    };
                    return (type_, origin);
                }
            }
            let type_ = self.eval_method_call(receiver_type, name, site, environment);
            let origin = if receiver_type.contains_any() {
                UntypedOrigin::Propagated
            } else {
                UntypedOrigin::FallbackCall
            };
            return (type_, origin);
        }

        if let Some(key) = self.receiver_method_key(receiver_node, receiver_type, name, environment)
        {
            if let Some((type_, declared)) = self.eval_resolved_receiver_call(
                node,
                name,
                &key,
                receiver_type,
                arguments,
                block,
                environment,
            ) {
                let origin = if declared {
                    UntypedOrigin::DeclaredSignature
                } else {
                    UntypedOrigin::InferredMethod
                };
                return (type_, origin);
            }
        }

        let type_ = self.eval_method_call(receiver_type, name, site, environment);
        let origin = if receiver_type.contains_any() {
            UntypedOrigin::Propagated
        } else {
            UntypedOrigin::FallbackCall
        };
        (type_, origin)
    }

    fn eval_resolved_receiver_call<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        key: &MethodKey,
        receiver_type: &Type,
        arguments: &CallArguments<'node>,
        block: Option<&Node<'node>>,
        environment: &mut Environment,
    ) -> Option<(Type, bool)> {
        self.record_method_dependency(key, environment);
        let inferred_accessor = self
            .resolve_method_key(key)
            .filter(|resolved| {
                self.methods
                    .get(resolved)
                    .is_some_and(|state| !state.explicit)
            })
            .and_then(|resolved| {
                self.accessors
                    .get(&resolved)
                    .copied()
                    .map(|accessor| (resolved, accessor))
            });
        if let Some((accessor_key, accessor)) = inferred_accessor {
            return Some((
                self.eval_accessor_call(
                    &accessor_key,
                    accessor,
                    &arguments.argument_types,
                    environment,
                ),
                false,
            ));
        }

        let signature = self.observe_call(key, arguments, block.is_some())?;
        let declared = self
            .resolve_method_key(key)
            .and_then(|resolved| self.methods.get(&resolved))
            .is_some_and(|state| state.explicit);
        let block_return_type = self.observe_block_call(
            key,
            block,
            &signature,
            arguments,
            Some(receiver_type),
            environment,
        );
        let type_ = self.invoke_signature(
            node,
            name,
            &signature,
            arguments,
            Some(receiver_type),
            block_return_type.as_ref(),
        );
        Some((type_, declared))
    }

    fn call_terminates<'node>(
        &self,
        call: &CallNode<'node>,
        environment: &Environment,
        receiver_type: &Type,
        type_: &Type,
    ) -> bool {
        let name = prism::constant_name(call.name());
        if call.receiver().is_none()
            && matches!(name.as_str(), "raise" | "fail" | "abort" | "exit" | "exit!")
        {
            return true;
        }
        if call.receiver().as_ref().is_some_and(|receiver| {
            self.constant_reference_name(receiver)
                .is_some_and(|name| name.trim_start_matches("::") == "T")
        }) {
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

    fn observe_call(
        &mut self,
        key: &MethodKey,
        arguments: &CallArguments<'_>,
        has_block: bool,
    ) -> Option<MethodSig> {
        let key = self.resolve_method_key(key)?;
        if let Some(state) = self.methods.get(&key).filter(|state| state.explicit) {
            let fallback = state.call_signature();
            let overloads = if state.overloads.is_empty() {
                vec![fallback.clone()]
            } else {
                state.overloads.clone()
            };
            return Some(
                self.select_overload(&overloads, arguments, has_block)
                    .unwrap_or(fallback),
            );
        }
        let (signature, changed) = {
            let state = self.methods.get_mut(&key)?;
            let mut changed = false;
            let positional_types = if state.accepts_keyword_rest || !state.keywords.is_empty() {
                &arguments.positional_types
            } else {
                &arguments.argument_types
            };
            if !arguments.forwards_arguments
                && !arguments.has_unknown_positional_splat
                && !arguments.has_unknown_keyword_splat
            {
                changed |= state.observe_arguments(positional_types);
                if state.accepts_keyword_rest || !state.keywords.is_empty() {
                    for argument in &arguments.keyword_arguments {
                        changed |= state.observe_keyword(&argument.name, &argument.type_);
                    }
                }
            }
            (state.call_signature(), changed)
        };
        if changed {
            self.changed_methods.insert(key);
        }
        Some(signature)
    }

    fn observe_block_call<'node>(
        &mut self,
        key: &MethodKey,
        block: Option<&Node<'node>>,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        environment: &mut Environment,
    ) -> Option<Type> {
        let Some(block) = block else {
            return None;
        };
        let Some(key) = self.resolve_method_key(key) else {
            return None;
        };
        let mut bindings = self.infer_type_parameter_bindings(signature, arguments, None);
        bindings.extend(self.infer_generic_member_bindings(signature, arguments, receiver_type));
        let block_signature = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                receiver_type,
                &bindings,
                &signature.type_parameters,
            )
        });
        let expected = block_signature
            .as_ref()
            .and_then(|block| match block {
                Type::Proc(parameters, _) => Some(parameters.clone()),
                _ => None,
            })
            .unwrap_or_else(|| {
                self.methods
                    .get(&key)
                    .map_or_else(Vec::new, MethodState::block_parameters)
            });
        let block_type = self.eval_block_node(block, &expected, environment);
        let mut checked_bindings =
            self.infer_type_parameter_bindings(signature, arguments, Some(&block_type));
        checked_bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            receiver_type,
        ));
        let checked_block_signature = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                receiver_type,
                &checked_bindings,
                &signature.type_parameters,
            )
        });
        if let Some(Type::Proc(_, expected_return)) = checked_block_signature.as_ref() {
            if !expected_return.is_any()
                && !expected_return.is_nil()
                && !self.is_assignable(&block_type, expected_return)
            {
                self.check_assignable(block, &block_type, expected_return);
            }
        }
        if self.methods.get(&key).is_some_and(|state| !state.explicit)
            && self
                .methods
                .get_mut(&key)
                .is_some_and(|state| state.observe_block_return(&block_type))
        {
            self.changed_methods.insert(key);
        }
        Some(block_type)
    }

    fn select_overload(
        &self,
        overloads: &[MethodSig],
        arguments: &CallArguments<'_>,
        has_block: bool,
    ) -> Option<MethodSig> {
        overloads
            .iter()
            .find(|signature| {
                (!has_block || signature.block.is_some())
                    && self.signature_accepts_arguments(signature, arguments)
            })
            .or_else(|| {
                overloads
                    .iter()
                    .find(|signature| self.signature_accepts_arguments(signature, arguments))
            })
            .cloned()
    }

    fn signature_accepts_arguments(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
    ) -> bool {
        if arguments.forwards_arguments
            || arguments.has_dynamic_positional_splat
            || arguments.has_dynamic_keyword_splat
            || arguments.has_unknown_positional_splat
            || arguments.has_unknown_keyword_splat
        {
            return true;
        }
        let keyword_mode = !signature.keywords.is_empty() || signature.accepts_keyword_rest;
        let positional_types = if keyword_mode {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        if positional_types.len() < signature.required_params
            || (!signature.accepts_rest && positional_types.len() > signature.params.len())
        {
            return false;
        }
        if keyword_mode && !arguments.has_keyword_splat {
            let provided = arguments
                .keyword_arguments
                .iter()
                .map(|argument| argument.name.as_str())
                .collect::<BTreeSet<_>>();
            if signature
                .keywords
                .iter()
                .any(|(name, parameter)| parameter.required && !provided.contains(name.as_str()))
            {
                return false;
            }
            if !signature.accepts_keyword_rest
                && arguments
                    .keyword_arguments
                    .iter()
                    .any(|argument| !signature.keywords.contains_key(&argument.name))
            {
                return false;
            }
        }
        let type_parameter_bindings =
            self.infer_type_parameter_bindings(signature, arguments, None);
        if !positional_types.iter().enumerate().all(|(index, actual)| {
            let Some(expected) = signature.positional_type(index, positional_types.len()) else {
                return false;
            };
            let expected = self.substitute_signature_type(
                expected,
                None,
                &type_parameter_bindings,
                &signature.type_parameters,
            );
            self.is_assignable(actual, &expected)
        }) {
            return false;
        }
        if keyword_mode
            && !arguments.has_keyword_splat
            && !arguments.keyword_arguments.iter().all(|argument| {
                signature
                    .keywords
                    .get(&argument.name)
                    .is_some_and(|expected| {
                        let expected = self.substitute_signature_type(
                            &expected.type_,
                            None,
                            &type_parameter_bindings,
                            &signature.type_parameters,
                        );
                        self.is_assignable(&argument.type_, &expected)
                    })
                    || signature.accepts_keyword_rest
            })
        {
            return false;
        }
        true
    }

    fn record_method_dependency(&mut self, key: &MethodKey, environment: &Environment) {
        let Some(callee) = self.resolve_method_key(key) else {
            return;
        };
        let Some(caller) = environment.method_key.as_ref() else {
            return;
        };
        if self.methods.contains_key(caller) {
            self.method_callers
                .entry(callee)
                .or_default()
                .insert(caller.clone());
        }
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
            let owner = self.resolve_global_name(owner);
            self.append_method_candidates(
                &owner,
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
                for module in info.extends.iter().rev() {
                    self.append_method_candidates(module, name, false, visited, candidates);
                }
            }
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
        arguments: &CallArguments<'node>,
        environment: &Environment,
    ) {
        let key = MethodKey {
            owner: Some(owner.to_owned()),
            name: "initialize".to_owned(),
            singleton: false,
        };
        self.record_method_dependency(&key, environment);
        if let Some(signature) = self.observe_call(&key, arguments, false) {
            let receiver_type = Type::named(owner.to_owned());
            let _ = self.invoke_signature(
                node,
                "initialize",
                &signature,
                arguments,
                Some(&receiver_type),
                None,
            );
        }
    }

    fn implicit_method_key(&self, name: &str, environment: &Environment) -> MethodKey {
        if let Some(current) = &environment.method_key {
            let owner = if current.singleton {
                current.owner.clone()
            } else {
                Self::named_type_name(&environment.self_type).or_else(|| current.owner.clone())
            };
            MethodKey {
                owner,
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
        let (owner, class_object) = if let Some(owner) = Self::class_object_owner(receiver_type) {
            (owner, true)
        } else if let Type::Named(owner, _) = receiver_type {
            (owner.clone(), false)
        } else {
            return None;
        };
        let singleton = if class_object {
            true
        } else if receiver_node.is_some_and(|node| node.as_self_node().is_some()) {
            environment
                .method_key
                .as_ref()
                .is_some_and(|key| key.singleton)
        } else {
            receiver_node.is_some_and(|node| self.constant_reference_name(node).is_some())
        };
        Some(MethodKey {
            owner: Some(owner),
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

    fn begin_method_evaluation(&mut self, method: &MethodKey) {
        let Some(shared_keys) = self.method_shared_reads.remove(method) else {
            return;
        };
        for shared_key in shared_keys {
            let empty = self
                .shared_readers
                .get_mut(&shared_key)
                .is_some_and(|readers| {
                    readers.remove(method);
                    readers.is_empty()
                });
            if empty {
                self.shared_readers.remove(&shared_key);
            }
        }
    }

    fn record_shared_read(&mut self, key: SharedKey, environment: &Environment) {
        let Some(method) = environment.method_key.as_ref() else {
            return;
        };
        if !self.methods.contains_key(method) {
            return;
        }
        self.method_shared_reads
            .entry(method.clone())
            .or_default()
            .insert(key.clone());
        self.shared_readers
            .entry(key)
            .or_default()
            .insert(method.clone());
    }

    fn observe_ivar(&mut self, environment: &Environment, name: String, actual: &Type) {
        let Some(key) = self.ivar_key(environment, &name) else {
            return;
        };
        let next = self
            .ivars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.ivars.get(&key) != Some(&next) {
            self.ivars.insert(key.clone(), next);
            self.changed_shared.insert(SharedKey::Ivar(key));
        }
    }

    fn preserve_typed_empty_array_ivar<'node>(
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

    fn ivar_type(&mut self, environment: &Environment, name: &str) -> Type {
        let Some(key) = self.ivar_key(environment, name) else {
            return Type::Any;
        };
        self.record_shared_read(SharedKey::Ivar(key.clone()), environment);
        let refinement = ivar_refinement_key(name);
        if environment.contains(&refinement) {
            return environment.get(&refinement);
        }
        self.ivars.get(&key).cloned().unwrap_or(Type::Any)
    }

    fn inferred_accessor_ivar_type(
        &mut self,
        class: &str,
        name: &str,
        singleton: bool,
        environment: &Environment,
    ) -> Option<Type> {
        let mut owner = Some(class.to_owned());
        let mut visited = BTreeSet::new();
        while let Some(current) = owner {
            if !visited.insert(current.clone()) {
                break;
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
            owner = self
                .classes
                .get(&current)
                .and_then(|info| info.superclass.clone());
        }
        None
    }

    fn observe_accessor_ivar(&mut self, owner: &str, name: &str, singleton: bool, actual: &Type) {
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
            self.changed_shared.insert(SharedKey::Ivar(key));
        }
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

    fn scoped_constant_name(&self, environment: &Environment, name: &str) -> String {
        let absolute = name.trim_start().starts_with("::");
        let name = name.trim_start_matches("::");
        if absolute || name.contains("::") {
            return name.to_owned();
        }
        self.lexical_owner(environment)
            .map_or_else(|| name.to_owned(), |owner| format!("{owner}::{name}"))
    }

    fn struct_subclass_type<'node>(
        &self,
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
        Some(Type::named(self.constant_key(environment, constant_name)))
    }

    fn observe_constant(&mut self, environment: &Environment, name: String, actual: &Type) {
        let key = self.constant_key(environment, &name);
        let next = self
            .constants
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.constants.get(&key) != Some(&next) {
            self.constants.insert(key.clone(), next);
            self.changed_shared.insert(SharedKey::Constant(key));
        }
    }

    fn constant_type(&mut self, environment: &Environment, name: &str) -> Type {
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
                .classes
                .get(&current)
                .and_then(|info| info.superclass.clone());
        }

        // A qualified constant reference such as `Color::BLUE` is still
        // resolved lexically.  Do this before the suffix-based fallback,
        // because a workspace may contain another `Color::BLUE` (for example
        // `Thor::Shell::Color::BLUE`) that makes the suffix ambiguous.
        let resolved = self.resolve_name(name, result_owner.as_deref());
        if self.constants.contains_key(&resolved) && !candidates.contains(&resolved) {
            candidates.push(resolved.clone());
        }

        let selected = candidates
            .iter()
            .position(|candidate| self.constants.contains_key(candidate));
        let read_count = selected.map_or(candidates.len(), |index| index + 1);
        for candidate in candidates.iter().take(read_count) {
            self.record_shared_read(SharedKey::Constant(candidate.clone()), environment);
        }
        if let Some(index) = selected {
            if let Some(type_) = self.constants.get(&candidates[index]) {
                return self.resolve_type_names(type_, result_owner.as_deref());
            }
        }
        if resolved != name
            || self.classes.contains_key(&resolved)
            || Self::looks_like_class_name(&resolved)
        {
            Self::class_object_type(&resolved)
        } else {
            signature::parse_type(name)
        }
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
        if self.class_vars.get(&key) != Some(&next) {
            self.class_vars.insert(key.clone(), next);
            self.changed_shared.insert(SharedKey::ClassVar(key));
        }
    }

    fn class_var_type(&mut self, environment: &Environment, name: &str) -> Type {
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

    fn observe_global(&mut self, name: String, actual: &Type) {
        let next = self
            .globals
            .get(&name)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.globals.get(&name) != Some(&next) {
            self.globals.insert(name.clone(), next);
            self.changed_shared.insert(SharedKey::Global(name));
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
                .and_then(|type_| {
                    Self::class_object_value_type(type_).or_else(|| Some(type_.clone()))
                })
                .map_or(Type::Any, |type_| Type::union([Type::Nil, type_])),
            "any" => Type::union(value_types()),
            "all" => Type::intersection(value_types()),
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
        block: Option<&Node<'node>>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "puts" | "print" | "p" | "pp" | "warn" => Type::Nil,
            "require" | "require_relative" | "load" => Type::bool(),
            "raise" | "fail" | "abort" | "exit" | "exit!" => Type::Never,
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
            "Hash" => {
                if let Some(block) = block {
                    let hash = Type::Hash(Box::new(Type::Any), Box::new(Type::Any));
                    let _ = self.eval_block_node(block, &[hash, Type::Any], environment);
                }
                Type::Hash(Box::new(Type::Any), Box::new(Type::Any))
            }
            "lambda" | "proc" => Type::Proc(Vec::new(), Box::new(Type::Any)),
            "rand" => Type::Float,
            "sleep" => Type::Integer,
            "include" | "prepend" | "extend" | "alias_method" | "attr_reader" | "attr_writer"
            | "attr_accessor" | "private" | "protected" | "public" | "module_function"
            | "refine" => Type::Nil,
            "id" | "object_id" | "hash" => Type::Integer,
            _ => {
                let _ = (node, argument_nodes, environment);
                Type::Any
            }
        }
    }

    fn eval_accessor_call(
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
                .inferred_accessor_ivar_type(owner, name, key.singleton, environment)
                .unwrap_or(Type::Any),
            AccessorKind::Writer => {
                let type_ = argument_types.first().cloned().unwrap_or(Type::Any);
                self.observe_accessor_ivar(owner, name, key.singleton, &type_);
                type_
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
            if let Some(block) = site.block {
                let _ = self.eval_block_node(block, &[Type::Any], environment);
            }
            return Type::Never;
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
                Type::Proc(_, _) => Self::class_object_type("Proc"),
                Type::Object => Self::class_object_type("Object"),
                Type::Named(class, _) => Self::class_object_type(class),
                Type::Intersection(_) | Type::Union(_) | Type::TypeVar(_) | Type::AttachedClass => {
                    Type::Any
                }
            };
        }

        if matches!(
            name,
            "nil?" | "is_a?" | "kind_of?" | "instance_of?" | "==" | "!=" | "equal?" | "eql?" | "!"
        ) {
            return Type::bool();
        }

        if matches!(name, "id" | "object_id" | "hash") {
            return Type::Integer;
        }

        if name == "[]" {
            if let Type::Named(record, _) = receiver {
                if let Some(key) = site.argument_nodes.first() {
                    if let Some(type_) =
                        signature::parse_inline_record_field(record, &prism::text(self.source, key))
                    {
                        return type_;
                    }
                }
            }
        }

        match receiver {
            Type::Array(element) => self.eval_array_method(element, name, site, environment),
            Type::Tuple(elements) => {
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
                _ => self.eval_common_method(name),
            },
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
                    let _ = arguments;
                    instance
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
            Type::Named(class, arguments) if name == "new" => {
                if self
                    .classes
                    .get(class)
                    .is_some_and(|info| !info.type_members.is_empty())
                {
                    Type::Named(class.clone(), arguments.clone())
                } else {
                    Type::Named(class.clone(), Vec::new())
                }
            }
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
            Type::Any | Type::Object | Type::TypeVar(_) | Type::AttachedClass => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::Any], environment);
                }
                self.eval_common_method(name)
            }
            Type::Never | Type::Proc(_, _) | Type::Intersection(_) | Type::Union(_) => Type::Any,
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
            "map" | "collect" | "map!" | "collect!" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(element), environment)
                });
                Type::Array(Box::new(block_type))
            }
            "flat_map" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(element), environment)
                });
                Type::Array(Box::new(self.array_element_type(&block_type)))
            }
            "each_with_index" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let expected = vec![element.clone(), Type::Integer];
                    let _ = self.eval_block_node(block, &expected, environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "filter_map" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(element), environment)
                });
                Type::Array(Box::new(block_type.truthy_part()))
            }
            "flatten" => Type::Array(Box::new(self.flattened_array_element_type(element))),
            "each" | "select" | "filter" | "reject" | "sort" | "reverse" | "rotate" | "shuffle" => {
                if site.block.is_none() && matches!(name, "each" | "select" | "filter" | "reject") {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "reverse_each" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "uniq" => Type::Array(Box::new(element.clone())),
            "each_index" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::Integer], environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "find" | "detect" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, element.clone()])
            }
            "find_index" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, Type::Integer])
            }
            "index" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, Type::Integer])
            }
            "group_by" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let key = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(element), environment)
                });
                Type::Hash(
                    Box::new(key),
                    Box::new(Type::Array(Box::new(element.clone()))),
                )
            }
            "partition" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(Type::Array(Box::new(element.clone()))))
            }
            "take_while" | "drop_while" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "sort_by" | "sort_by!" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "first" | "last" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "shift" | "pop" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "at" => Type::union([Type::Nil, element.clone()]),
            "fetch" => {
                if let Some(default) = site.argument_types.get(1) {
                    element.join(default)
                } else if let Some(block) = site.block {
                    let block_type = self.eval_block_node(block, &[Type::Integer], environment);
                    element.join(&block_type)
                } else {
                    element.clone()
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
            "[]=" => site.argument_types.last().cloned().unwrap_or(Type::Any),
            "values_at" => Type::Array(Box::new(element.clone())),
            "sample" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "min" | "max" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "min_by" | "max_by" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, element.clone()])
            }
            "combination" | "repeated_combination" | "permutation" | "repeated_permutation" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let expected = Type::Array(Box::new(element.clone()));
                    let _ = self.eval_block_node(block, &[expected], environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "product" => {
                let mut tuple = vec![element.clone()];
                tuple.extend(
                    site.argument_types
                        .iter()
                        .map(|argument| self.array_element_type(argument)),
                );
                if let Some(block) = site.block {
                    let expected = Type::Array(Box::new(Type::Tuple(tuple.clone())));
                    let _ = self.eval_block_node(block, &[expected], environment);
                    Type::Array(Box::new(element.clone()))
                } else {
                    Type::Array(Box::new(Type::Tuple(tuple)))
                }
            }
            "pack" => Type::String,
            "compact" => Type::Array(Box::new(element.without(&Type::Nil))),
            "compact!" | "uniq!" => {
                Type::union([Type::Nil, Type::Array(Box::new(element.clone()))])
            }
            "length" | "size" => Type::Integer,
            "count" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Integer
            }
            "empty?" | "include?" => Type::bool(),
            "any?" | "all?" | "none?" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::bool()
            }
            "join" => Type::String,
            "concat" => {
                let element = site
                    .argument_types
                    .iter()
                    .fold(element.clone(), |current, actual| {
                        current.join(&self.array_element_type(actual))
                    });
                Type::Array(Box::new(element))
            }
            "zip" => {
                let mut tuple = vec![element.clone()];
                tuple.extend(
                    site.argument_types
                        .iter()
                        .map(|argument| self.array_element_type(argument)),
                );
                Type::Array(Box::new(Type::Tuple(tuple)))
            }
            "sum" => {
                let element = site.block.map_or_else(
                    || element.clone(),
                    |block| self.eval_block_node(block, std::slice::from_ref(element), environment),
                );
                Self::numeric_sum_type(&element, site.argument_types.first())
            }
            "+" | "|" => {
                let element = site
                    .argument_types
                    .iter()
                    .fold(element.clone(), |current, actual| {
                        current.join(&self.array_element_type(actual))
                    });
                Type::Array(Box::new(element))
            }
            "-" | "&" => Type::Array(Box::new(element.clone())),
            "*" => match site.argument_types.first() {
                Some(Type::Integer) => Type::Array(Box::new(element.clone())),
                Some(Type::String) => Type::String,
                _ => Type::Any,
            },
            "take" | "drop" => Type::Array(Box::new(element.clone())),
            "fill" | "replace" | "clear" | "unshift" | "prepend" | "insert" | "reverse!"
            | "rotate!" | "shuffle!" | "sort!" => Type::Array(Box::new(element.clone())),
            "select!" | "filter!" | "reject!" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, Type::Array(Box::new(element.clone()))])
            }
            "keep_if" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "bsearch" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, element.clone()])
            }
            "push" | "<<" => {
                for (argument, actual) in site.argument_nodes.iter().zip(site.argument_types) {
                    self.check_assignable(argument, actual, element);
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
            "[]" | "default" => Type::union([Type::Nil, value.clone()]),
            "dig" => Type::union([Type::Nil, value.clone()]),
            "[]=" => site.argument_types.last().cloned().unwrap_or(Type::Any),
            "fetch" => {
                if let Some(default) = site.argument_types.get(1) {
                    value.join(default)
                } else if let Some(block) = site.block {
                    let block_type =
                        self.eval_block_node(block, std::slice::from_ref(key), environment);
                    value.join(&block_type)
                } else {
                    value.clone()
                }
            }
            "fetch_values" => Type::Array(Box::new(value.clone())),
            "map" | "collect" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, &[key.clone(), value.clone()], environment)
                });
                Type::Array(Box::new(block_type))
            }
            "keys" => Type::Array(Box::new(key.clone())),
            "values" => Type::Array(Box::new(value.clone())),
            "each" | "each_pair" | "each_key" | "each_value" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
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
            "merge" | "merge!" | "update" | "reverse_merge" => {
                let mut merged_key = key.clone();
                let mut merged_value = value.clone();
                for argument in site.argument_types {
                    match argument {
                        Type::Hash(argument_key, argument_value) => {
                            merged_key = merged_key.join(argument_key);
                            merged_value = merged_value.join(argument_value);
                        }
                        Type::Any => {
                            merged_key = Type::Any;
                            merged_value = Type::Any;
                        }
                        _ => {}
                    }
                }
                if let Some(block) = site.block {
                    let block_type = self.eval_block_node(
                        block,
                        &[merged_key.clone(), value.clone(), merged_value.clone()],
                        environment,
                    );
                    merged_value = merged_value.join(&block_type);
                }
                Type::Hash(Box::new(merged_key), Box::new(merged_value))
            }
            "dup" | "clone" | "to_h" | "slice" | "except" => {
                Type::Hash(Box::new(key.clone()), Box::new(value.clone()))
            }
            "compact" => Type::Hash(Box::new(key.clone()), Box::new(value.without(&Type::Nil))),
            "invert" => Type::Hash(Box::new(value.clone()), Box::new(key.clone())),
            "select" | "filter" | "reject" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[key.clone(), value.clone()], environment);
                }
                Type::Hash(Box::new(key.clone()), Box::new(value.clone()))
            }
            "sort_by" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[key.clone(), value.clone()], environment);
                }
                Type::Array(Box::new(Type::Tuple(vec![key.clone(), value.clone()])))
            }
            "transform_keys" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(key), environment)
                });
                Type::Hash(Box::new(block_type), Box::new(value.clone()))
            }
            "transform_values" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(value), environment)
                });
                Type::Hash(Box::new(key.clone()), Box::new(block_type))
            }
            "to_a" => Type::Array(Box::new(Type::Tuple(vec![key.clone(), value.clone()]))),
            "values_at" => Type::Array(Box::new(value.clone())),
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

    fn eval_string_method<'a, 'node>(
        &mut self,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "length" | "size" | "bytesize" | "count" => Type::Integer,
            "empty?" | "start_with?" | "end_with?" | "include?" => Type::bool(),
            "to_i" | "to_int" => Type::Integer,
            "to_f" => Type::Float,
            "to_r" => Type::named("Rational"),
            "to_c" => Type::named("Complex"),
            "to_sym" | "intern" => Type::Symbol,
            "split" | "chars" | "lines" => Type::Array(Box::new(Type::String)),
            "bytes" | "codepoints" => Type::Array(Box::new(Type::Integer)),
            "[]" | "slice" | "byteslice" => Type::union([Type::Nil, Type::String]),
            "match" => Type::union([Type::Nil, Type::named("MatchData")]),
            "match?" => Type::bool(),
            "=~" => Type::union([Type::Nil, Type::Integer]),
            "delete_prefix" | "delete_suffix" | "inspect" | "dump" | "to_str" => Type::String,
            "+@" => Type::String,
            "index" | "rindex" => Type::union([Type::Nil, Type::Integer]),
            "encode" | "reverse" | "reverse!" | "strip" | "lstrip" | "rstrip" | "upcase"
            | "downcase" | "capitalize" | "swapcase" | "chomp" | "chop" | "succ" | "next"
            | "delete" | "tr" | "tr_s" | "squeeze" | "scrub" | "center" | "ljust" | "rjust"
            | "prepend" | "concat" | "replace" | "force_encoding" | "to_s" | "dup" | "clone"
            | "+" | "*" | "<<" => Type::String,
            "gsub" | "sub" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::String], environment);
                }
                Type::String
            }
            "each_line" | "each_char" | "each_byte" | "scan" => {
                if let Some(block) = site.block {
                    let element = if name == "each_byte" {
                        Type::Integer
                    } else {
                        Type::String
                    };
                    let _ = self.eval_block_node(block, &[element], environment);
                }
                Type::String
            }
            "chr" => Type::String,
            "ord" => Type::Integer,
            _ => Type::Any,
        }
    }

    fn eval_numeric_method(
        &mut self,
        receiver: Type,
        name: &str,
        argument_types: &[Type],
        block: Option<&Node<'_>>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "times" | "upto" | "downto" | "step" => {
                let Some(block) = block else {
                    return Type::named("Enumerator");
                };
                let _ = self.eval_block_node(block, std::slice::from_ref(&receiver), environment);
                receiver
            }
            "+@" | "-@" => receiver,
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
            "finite?" | "nan?" | "real?" | "complex?" => Type::bool(),
            "infinite?" => Type::union([Type::Nil, Type::Integer]),
            "abs" | "magnitude" => receiver,
            "fdiv" => Type::Float,
            "div" | "bit_length" | "numerator" | "denominator" => Type::Integer,
            "divmod" => Type::Array(Box::new(Type::Tuple(vec![Type::Integer, Type::Integer]))),
            "gcdlcm" => Type::Array(Box::new(Type::Integer)),
            "round" | "ceil" | "floor" | "truncate" => {
                if argument_types.is_empty() {
                    Type::Integer
                } else {
                    Type::Float
                }
            }
            "next" | "succ" | "pred" => receiver,
            "gcd" | "lcm" => Type::Integer,
            "digits" => Type::Array(Box::new(Type::Integer)),
            "clamp" => receiver,
            "to_f" => Type::Float,
            "to_i" | "to_int" => Type::Integer,
            "to_r" => Type::named("Rational"),
            "to_c" => Type::named("Complex"),
            "real" => receiver,
            "imag" => Type::Integer,
            "to_s" => Type::String,
            _ => Type::Any,
        }
    }

    fn eval_common_method(&self, name: &str) -> Type {
        match name {
            "to_s" => Type::String,
            "id" | "object_id" | "hash" => Type::Integer,
            "respond_to?" | "frozen?" => Type::bool(),
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

    fn inferred_block_signature<'node>(node: &Node<'node>) -> MethodSig {
        let parameters = node
            .as_block_node()
            .and_then(|block| block.parameters())
            .and_then(|parameters| {
                parameters
                    .as_block_parameters_node()
                    .and_then(|parameters| parameters.parameters())
                    .or_else(|| parameters.as_parameters_node())
            });
        MethodState::inferred(parameters).body_signature()
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
                let expected = Self::destructure_block_parameters(&parameters, expected);
                self.bind_parameters(
                    Some(parameters),
                    Some(&MethodSig::new(expected, Type::Any)),
                    &mut environment,
                );
            } else if let Some(parameters) = parameters.as_parameters_node() {
                let expected = Self::destructure_block_parameters(&parameters, expected);
                self.bind_parameters(
                    Some(parameters),
                    Some(&MethodSig::new(expected, Type::Any)),
                    &mut environment,
                );
            } else if parameters.as_it_parameters_node().is_some()
                || parameters.as_numbered_parameters_node().is_some()
            {
                for (index, type_) in expected.iter().enumerate() {
                    environment.bind(format!("_{}", index + 1), type_.clone());
                }
                if let Some(type_) = expected.first() {
                    environment.bind("it", type_.clone());
                }
            }
        } else {
            for (index, type_) in expected.iter().enumerate() {
                environment.bind(format!("_{}", index + 1), type_.clone());
            }
            if let Some(type_) = expected.first() {
                environment.bind("it", type_.clone());
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

    fn destructure_block_parameters<'node>(
        parameters: &ParametersNode<'node>,
        expected: &[Type],
    ) -> Vec<Type> {
        if parameters.requireds().len() > 1 {
            if let [Type::Tuple(elements)] = expected {
                return elements.clone();
            }
        }
        expected.to_vec()
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
        arguments: &CallArguments<'node>,
        receiver_type: Option<&Type>,
        block_return_type: Option<&Type>,
    ) -> Type {
        let mut type_parameter_bindings =
            self.infer_type_parameter_bindings(signature, arguments, block_return_type);
        type_parameter_bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            receiver_type,
        ));
        let keyword_mode = !signature.keywords.is_empty() || signature.accepts_keyword_rest;
        let argument_types = if keyword_mode {
            &arguments.positional_types
        } else {
            &arguments.argument_types
        };
        let mut dynamic_splat_shape_error = false;
        if arguments.has_dynamic_positional_splat {
            let expected_rest = signature
                .accepts_rest
                .then_some(signature.rest_index)
                .flatten()
                .filter(|index| *index == 0)
                .and_then(|_| signature.params.first())
                .map(|expected| {
                    self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    )
                });
            if let Some(expected) = expected_rest {
                for splat_type in &arguments.dynamic_positional_splat_types {
                    if let Type::Array(element) = splat_type {
                        if !self.is_assignable(element, &expected) {
                            self.check_assignable(node, element, &expected);
                        }
                    } else {
                        dynamic_splat_shape_error = true;
                    }
                }
            } else {
                dynamic_splat_shape_error = true;
            }
            if dynamic_splat_shape_error {
                self.error(
                    node,
                    "Splats are only supported where the size of the array is known statically",
                );
            }
        }
        if arguments.has_dynamic_keyword_splat {
            self.error(
                node,
                "Keyword args with splats are only supported where the shape of the hash is known statically",
            );
        }
        let positional_error = !arguments.forwards_arguments
            && !arguments.has_dynamic_positional_splat
            && !arguments.has_unknown_positional_splat
            && (argument_types.len() < signature.required_params
                || (!signature.accepts_rest && argument_types.len() > signature.params.len()));
        let provided_keywords = arguments
            .keyword_arguments
            .iter()
            .map(|argument| argument.name.as_str())
            .collect::<BTreeSet<_>>();
        let missing_keywords = !arguments.forwards_arguments
            && keyword_mode
            && !arguments.has_keyword_splat
            && signature.keywords.iter().any(|(name, parameter)| {
                parameter.required && !provided_keywords.contains(name.as_str())
            });
        let unknown_keyword = !arguments.forwards_arguments
            && keyword_mode
            && !signature.accepts_keyword_rest
            && arguments
                .keyword_arguments
                .iter()
                .any(|argument| !signature.keywords.contains_key(&argument.name));

        if positional_error || missing_keywords || unknown_keyword {
            let expected = if keyword_mode {
                let required_keywords = signature
                    .keywords
                    .iter()
                    .filter_map(|(name, parameter)| parameter.required.then_some(name.as_str()))
                    .collect::<Vec<_>>();
                if required_keywords.is_empty() {
                    signature.params.len().to_string()
                } else {
                    format!(
                        "at least {} positional arguments and keywords ({})",
                        signature.required_params,
                        required_keywords.join(", ")
                    )
                }
            } else if signature.required_params == signature.params.len() && !signature.accepts_rest
            {
                signature.params.len().to_string()
            } else {
                format!("at least {}", signature.required_params)
            };
            self.error(
                node,
                format!(
                    "Wrong number of arguments for `{name}`: expected {expected}, found {}",
                    argument_types.len() + arguments.keyword_arguments.len()
                ),
            );
        }
        if keyword_mode
            && !arguments.forwards_arguments
            && !arguments.has_unknown_positional_splat
            && !arguments.has_unknown_keyword_splat
        {
            for (index, (argument_index, actual)) in arguments
                .positional_indices
                .iter()
                .zip(argument_types)
                .enumerate()
            {
                if let (Some(argument), Some(expected)) = (
                    arguments.argument_nodes.get(*argument_index),
                    signature.positional_type(index, argument_types.len()),
                ) {
                    let expected = self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    self.check_assignable(argument, actual, &expected);
                }
            }
        } else if !arguments.forwards_arguments
            && !arguments.has_unknown_positional_splat
            && !arguments.has_unknown_keyword_splat
        {
            for (index, (argument_index, actual)) in arguments
                .argument_indices
                .iter()
                .zip(argument_types)
                .enumerate()
            {
                if let (Some(argument), Some(expected)) = (
                    arguments.argument_nodes.get(*argument_index),
                    signature.positional_type(index, argument_types.len()),
                ) {
                    let expected = self.substitute_signature_type(
                        expected,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    self.check_assignable(argument, actual, &expected);
                }
            }
        }
        if keyword_mode && !arguments.forwards_arguments && !arguments.has_unknown_keyword_splat {
            for argument in &arguments.keyword_arguments {
                if let Some(expected) = signature.keywords.get(&argument.name) {
                    let expected = self.substitute_signature_type(
                        &expected.type_,
                        receiver_type,
                        &type_parameter_bindings,
                        &signature.type_parameters,
                    );
                    self.check_assignable(&argument.node, &argument.type_, &expected);
                }
            }
        }
        if arguments.has_unknown_positional_splat || arguments.has_unknown_keyword_splat {
            Type::Any
        } else {
            self.substitute_signature_type(
                &signature.return_type,
                receiver_type,
                &type_parameter_bindings,
                &signature.type_parameters,
            )
        }
    }

    fn check_assignable<'node>(&mut self, node: &Node<'node>, actual: &Type, expected: &Type) {
        if !self.is_assignable(actual, expected) {
            self.error(node, format!("Expected `{expected}`, but found `{actual}`"));
        }
    }

    fn resolve_signature_names(&self, signature: &MethodSig, owner: Option<&str>) -> MethodSig {
        let mut result = signature.clone();
        result.params = signature
            .params
            .iter()
            .map(|type_| {
                self.resolve_type_names_with_locals(type_, owner, &signature.type_parameters)
            })
            .collect();
        result.return_type = self.resolve_type_names_with_locals(
            &signature.return_type,
            owner,
            &signature.type_parameters,
        );
        result.keywords = signature
            .keywords
            .iter()
            .map(|(name, parameter)| {
                (
                    name.clone(),
                    signature::KeywordParam {
                        type_: self.resolve_type_names_with_locals(
                            &parameter.type_,
                            owner,
                            &signature.type_parameters,
                        ),
                        required: parameter.required,
                    },
                )
            })
            .collect();
        result.block = signature.block.as_ref().map(|block| {
            self.resolve_type_names_with_locals(block, owner, &signature.type_parameters)
        });
        result
    }

    fn resolve_type_names(&self, type_: &Type, owner: Option<&str>) -> Type {
        self.resolve_type_names_with_locals(type_, owner, &[])
    }

    fn resolve_type_names_with_locals(
        &self,
        type_: &Type,
        owner: Option<&str>,
        local_type_parameters: &[String],
    ) -> Type {
        match type_ {
            Type::Symbol
                if owner
                    .and_then(|owner| {
                        let resolved = self.resolve_name("Symbol", Some(owner));
                        (resolved != "Symbol" && self.classes.contains_key(&resolved))
                            .then_some(resolved)
                    })
                    .is_some() =>
            {
                Type::Named(self.resolve_name("Symbol", owner), Vec::new())
            }
            Type::TypeVar(name)
                if !local_type_parameters
                    .iter()
                    .any(|parameter| parameter == name)
                    && owner.is_some_and(|owner| {
                        self.classes
                            .get(owner)
                            .is_some_and(|info| info.type_members.contains_key(name))
                    }) =>
            {
                Type::TypeVar(format!(
                    "{}::{name}",
                    owner.expect("owner is present for a type member")
                ))
            }
            Type::Named(name, arguments) => {
                if arguments.is_empty()
                    && owner.is_some_and(|owner| {
                        self.classes
                            .get(owner)
                            .is_some_and(|info| info.type_members.contains_key(name))
                    })
                {
                    return Type::TypeVar(format!(
                        "{}::{name}",
                        owner.expect("owner is present for a type member")
                    ));
                }
                if arguments.is_empty() {
                    if let Some((alias_name, alias_type)) = self.find_type_alias(name, owner) {
                        if alias_type != *type_ {
                            let alias_owner = alias_name.rsplit_once("::").map(|(scope, _)| scope);
                            return self.resolve_type_names_with_locals(
                                &alias_type,
                                alias_owner.or(owner),
                                local_type_parameters,
                            );
                        }
                    }
                }
                let resolved = if name == "instance" && arguments.is_empty() {
                    name.clone()
                } else {
                    self.resolve_name(name, owner)
                };
                Type::Named(
                    resolved,
                    arguments
                        .iter()
                        .map(|argument| {
                            self.resolve_type_names_with_locals(
                                argument,
                                owner,
                                local_type_parameters,
                            )
                        })
                        .collect(),
                )
            }
            Type::Array(element) => Type::Array(Box::new(self.resolve_type_names_with_locals(
                element,
                owner,
                local_type_parameters,
            ))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(self.resolve_type_names_with_locals(key, owner, local_type_parameters)),
                Box::new(self.resolve_type_names_with_locals(value, owner, local_type_parameters)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        self.resolve_type_names_with_locals(element, owner, local_type_parameters)
                    })
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| {
                        self.resolve_type_names_with_locals(parameter, owner, local_type_parameters)
                    })
                    .collect(),
                Box::new(self.resolve_type_names_with_locals(result, owner, local_type_parameters)),
            ),
            Type::Union(members) => Type::union(members.iter().map(|member| {
                self.resolve_type_names_with_locals(member, owner, local_type_parameters)
            })),
            Type::Intersection(members) => Type::intersection(members.iter().map(|member| {
                self.resolve_type_names_with_locals(member, owner, local_type_parameters)
            })),
            other => other.clone(),
        }
    }

    fn find_type_alias(&self, name: &str, owner: Option<&str>) -> Option<(String, Type)> {
        let name = name.trim_start_matches("::");
        let matches = |candidate: &str| candidate.eq_ignore_ascii_case(name);
        if let Some((key, type_)) = self.type_aliases.iter().find(|(key, _)| matches(key)) {
            return Some((key.clone(), type_.clone()));
        }

        let mut scope = owner;
        while let Some(current) = scope {
            let candidate = format!("{current}::{name}");
            if let Some((key, type_)) = self
                .type_aliases
                .iter()
                .find(|(key, _)| key.eq_ignore_ascii_case(&candidate))
            {
                return Some((key.clone(), type_.clone()));
            }
            scope = current.rsplit_once("::").map(|(parent, _)| parent);
        }

        let qualified_suffix = format!("::{name}");
        let mut qualified = self.type_aliases.iter().filter(|(key, _)| {
            key.to_ascii_lowercase()
                .ends_with(&qualified_suffix.to_ascii_lowercase())
        });
        if let Some((key, type_)) = qualified.next() {
            if qualified.next().is_none() {
                return Some((key.clone(), type_.clone()));
            }
        }

        let name_tail = name.rsplit_once("::").map_or(name, |(_, tail)| tail);
        let mut candidates = self.type_aliases.iter().filter(|(key, _)| {
            key.rsplit_once("::")
                .map_or(key.as_str(), |(_, tail)| tail)
                .eq_ignore_ascii_case(name_tail)
        });
        let (key, type_) = candidates.next()?;
        if candidates.next().is_some() {
            None
        } else {
            Some((key.clone(), type_.clone()))
        }
    }

    fn resolve_name(&self, name: &str, owner: Option<&str>) -> String {
        let name = name.trim_start_matches("::");
        let mut scope = owner;
        while let Some(current) = scope {
            let candidate = format!("{current}::{name}");
            if self.classes.contains_key(&candidate) || self.constants.contains_key(&candidate) {
                return candidate;
            }
            scope = current.rsplit_once("::").map(|(parent, _)| parent);
        }
        if self.classes.contains_key(name) || self.constants.contains_key(name) {
            return name.to_owned();
        }
        name.to_owned()
    }

    fn resolve_global_name(&self, name: &str) -> String {
        if self.classes.contains_key(name) {
            return name.to_owned();
        }
        let suffix = format!("::{name}");
        let mut matches = self
            .classes
            .keys()
            .filter(|candidate| candidate.ends_with(&suffix))
            .cloned();
        let Some(candidate) = matches.next() else {
            return name.to_owned();
        };
        if matches.next().is_none() {
            candidate
        } else {
            name.to_owned()
        }
    }

    fn nominal_name_candidates(&self, name: &str) -> Vec<String> {
        if self.classes.contains_key(name) || self.constants.contains_key(name) {
            return vec![name.to_owned()];
        }
        let suffix = format!("::{name}");
        let mut candidates = self
            .classes
            .keys()
            .filter(|candidate| candidate.ends_with(&suffix))
            .cloned()
            .collect::<Vec<_>>();
        candidates.extend(
            self.constants
                .keys()
                .filter(|candidate| candidate.ends_with(&suffix))
                .cloned(),
        );
        if candidates.is_empty() {
            candidates.push(name.to_owned());
        }
        candidates
    }

    fn nominal_names_match(&self, actual: &str, expected: &str) -> bool {
        if actual == expected {
            return true;
        }
        if self.nominal_name_candidates(actual).iter().any(|actual| {
            self.nominal_name_candidates(expected)
                .iter()
                .any(|expected| actual == expected)
        }) {
            return true;
        }
        let actual = self.resolve_global_name(actual);
        let expected = self.resolve_global_name(expected);
        actual == expected
            || (self.classes.contains_key(&actual) && expected.ends_with(&format!("::{actual}")))
            || (self.classes.contains_key(&expected) && actual.ends_with(&format!("::{expected}")))
    }

    fn normalize_class_graph(&mut self) {
        let owners = self.classes.keys().cloned().collect::<Vec<_>>();
        for owner in owners {
            let Some(info) = self.classes.get(&owner).cloned() else {
                continue;
            };
            let superclass = info
                .superclass
                .as_deref()
                .map(|name| self.resolve_name(name, Some(&owner)));
            let includes = info
                .includes
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            let prepends = info
                .prepends
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            let extends = info
                .extends
                .iter()
                .map(|name| self.resolve_name(name, Some(&owner)))
                .collect();
            if let Some(info) = self.classes.get_mut(&owner) {
                info.superclass = superclass;
                info.includes = includes;
                info.prepends = prepends;
                info.extends = extends;
            }
        }
    }

    fn is_assignable(&self, actual: &Type, expected: &Type) -> bool {
        let resolved_actual = self.resolve_type_names(actual, None);
        let resolved_expected = self.resolve_type_names(expected, None);
        if resolved_actual != *actual || resolved_expected != *expected {
            return self.is_assignable(&resolved_actual, &resolved_expected);
        }
        if actual.is_any() || expected.is_any() || actual.is_never() {
            return true;
        }
        if actual == expected || actual.is_subtype_of(expected) {
            return true;
        }
        match (actual, expected) {
            (Type::Union(actual_members), Type::Union(expected_members)) => {
                return actual_members.iter().all(|actual| {
                    expected_members
                        .iter()
                        .any(|expected| self.is_assignable(actual, expected))
                });
            }
            (Type::Union(actual_members), _) => {
                return actual_members
                    .iter()
                    .all(|member| self.is_assignable(member, expected));
            }
            (_, Type::Union(expected_members)) => {
                return expected_members
                    .iter()
                    .any(|member| self.is_assignable(actual, member));
            }
            _ => {}
        }
        if let Type::Intersection(expected_members) = expected {
            return expected_members
                .iter()
                .all(|member| self.is_assignable(actual, member));
        }
        if let Type::Intersection(actual_members) = actual {
            return actual_members
                .iter()
                .any(|member| self.is_assignable(member, expected));
        }
        match (actual, expected) {
            (Type::Array(actual), Type::Array(expected)) => self.is_assignable(actual, expected),
            (Type::Hash(actual_key, actual_value), Type::Hash(expected_key, expected_value)) => {
                self.is_assignable(actual_key, expected_key)
                    && self.is_assignable(actual_value, expected_value)
            }
            (Type::Tuple(actual), Type::Tuple(expected)) => {
                actual.len() == expected.len()
                    && actual
                        .iter()
                        .zip(expected)
                        .all(|(actual, expected)| self.is_assignable(actual, expected))
            }
            (Type::Array(actual), Type::Tuple(expected)) => expected
                .iter()
                .all(|expected| self.is_assignable(actual, expected)),
            (Type::Tuple(actual), Type::Array(expected)) => actual
                .iter()
                .all(|actual| self.is_assignable(actual, expected)),
            (_, Type::Named(name, arguments))
                if arguments.is_empty() && name_matches(name, "BasicObject") =>
            {
                true
            }
            (Type::Array(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Enumerable") =>
            {
                self.is_assignable(actual, &arguments[0])
            }
            (Type::Tuple(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Enumerable") =>
            {
                actual
                    .iter()
                    .all(|actual| self.is_assignable(actual, &arguments[0]))
            }
            (Type::Array(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Array") =>
            {
                self.is_assignable(actual, &arguments[0])
            }
            (Type::Tuple(actual), Type::Named(name, arguments))
                if arguments.len() == 1 && name_matches(name, "Array") =>
            {
                actual
                    .iter()
                    .all(|actual| self.is_assignable(actual, &arguments[0]))
            }
            (Type::Named(actual, _), Type::Array(_)) if self.nominal_subtype(actual, "Array") => {
                true
            }
            (Type::Hash(actual_key, actual_value), Type::Named(name, arguments))
                if arguments.len() == 2 && name_matches(name, "Hash") =>
            {
                self.is_assignable(actual_key, &arguments[0])
                    && self.is_assignable(actual_value, &arguments[1])
            }
            (Type::Named(actual, _), Type::Hash(_, _)) if self.nominal_subtype(actual, "Hash") => {
                true
            }
            (
                Type::Proc(actual_params, actual_return),
                Type::Proc(expected_params, expected_return),
            ) => {
                actual_params.len() == expected_params.len()
                    && actual_params
                        .iter()
                        .zip(expected_params)
                        .all(|(actual, expected)| self.is_assignable(expected, actual))
                    && self.is_assignable(actual_return, expected_return)
            }
            (Type::Named(actual_name, actual_args), Type::Named(expected_name, expected_args))
                if actual_args.len() == 1
                    && expected_args.is_empty()
                    && name_matches(actual_name, "Class")
                    && name_matches(expected_name, "Module") =>
            {
                true
            }
            (Type::Named(actual_name, actual_args), Type::Named(expected_name, expected_args)) => {
                if self.nominal_names_match(actual_name, expected_name) {
                    expected_args.is_empty()
                        || actual_args.is_empty()
                        || (actual_args.len() == expected_args.len()
                            && actual_args
                                .iter()
                                .zip(expected_args)
                                .all(|(actual, expected)| self.is_assignable(actual, expected)))
                } else {
                    expected_args.is_empty() && self.nominal_subtype(actual_name, expected_name)
                }
            }
            (Type::Named(actual, _), Type::Integer) if self.nominal_subtype(actual, "Integer") => {
                true
            }
            (Type::Named(actual, _), Type::Float) if self.nominal_subtype(actual, "Float") => true,
            (Type::Named(actual, _), Type::String) if self.nominal_subtype(actual, "String") => {
                true
            }
            (Type::Named(actual, _), Type::Symbol) if self.nominal_subtype(actual, "Symbol") => {
                true
            }
            _ => false,
        }
    }

    fn nominal_subtype(&self, actual: &str, expected: &str) -> bool {
        let actual_candidates = self.nominal_name_candidates(actual);
        let expected_candidates = self.nominal_name_candidates(expected);
        if expected_candidates
            .iter()
            .any(|expected| expected == "BasicObject")
        {
            return true;
        }
        actual_candidates.iter().any(|actual| {
            expected_candidates.iter().any(|expected| {
                if actual == expected {
                    return true;
                }
                let mut pending = vec![actual.clone()];
                let mut visited = BTreeSet::new();
                while let Some(name) = pending.pop() {
                    if !visited.insert(name.clone()) {
                        continue;
                    }
                    if name == *expected {
                        return true;
                    }
                    if let Some(superclass) = Self::builtin_superclass(&name) {
                        pending.push(superclass.to_owned());
                    }
                    let Some(info) = self.classes.get(&name) else {
                        continue;
                    };
                    if let Some(superclass) = &info.superclass {
                        pending.push(superclass.clone());
                    }
                    pending.extend(info.includes.iter().cloned());
                    pending.extend(info.prepends.iter().cloned());
                }
                false
            })
        })
    }

    fn builtin_superclass(name: &str) -> Option<&'static str> {
        match name.rsplit_once("::").map_or(name, |(_, tail)| tail) {
            "StandardError" => Some("Exception"),
            "ArgumentError" | "EncodingError" | "FiberError" | "IOError" | "IndexError"
            | "KeyError" | "LocalJumpError" | "NameError" | "NoMethodError" | "RangeError"
            | "RegexpError" | "RuntimeError" | "StopIteration" | "SystemCallError"
            | "TypeError" | "ZeroDivisionError" => Some("StandardError"),
            "EOFError" => Some("IOError"),
            "FloatDomainError" => Some("RangeError"),
            _ => None,
        }
    }

    fn apply_inline_assertion<'node>(&mut self, node: &Node<'node>, actual: Type) -> Type {
        if self.defer_inline_assertions {
            return actual;
        }
        let (start, end) = prism::span(node);
        let start_line = self.line_map.line_number(start);
        let end_line = self.line_map.line_number(end.saturating_sub(1));
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
        let expected = self.resolve_type_names(&assertion.type_, None);
        match assertion.kind {
            AssertionKind::Let => {
                self.check_assignable(node, &actual, &expected);
                expected
            }
            AssertionKind::Cast => expected,
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

    fn apply_inline_assertion_in_environment<'node>(
        &mut self,
        node: &Node<'node>,
        actual: Type,
        environment: &Environment,
    ) -> Type {
        if self.defer_inline_assertions {
            return actual;
        }
        let (start, end) = prism::span(node);
        let start_line = self.line_map.line_number(start);
        let end_line = self.line_map.line_number(end.saturating_sub(1));
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
        let owner = self.lexical_owner(environment);
        let expected = self.resolve_shadowed_builtin_types(&assertion.type_, owner.as_deref());
        match assertion.kind {
            AssertionKind::Let => {
                self.check_assignable(node, &actual, &expected);
                expected
            }
            AssertionKind::Cast => expected,
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

    fn resolve_shadowed_builtin_types(&self, type_: &Type, owner: Option<&str>) -> Type {
        match type_ {
            Type::Symbol => owner
                .and_then(|owner| {
                    let resolved = self.resolve_name("Symbol", Some(owner));
                    (resolved != "Symbol" && self.classes.contains_key(&resolved))
                        .then_some(Type::named(resolved))
                })
                .unwrap_or(Type::Symbol),
            Type::Array(element) => Type::Array(Box::new(
                self.resolve_shadowed_builtin_types(element, owner),
            )),
            Type::Hash(key, value) => Type::Hash(
                Box::new(self.resolve_shadowed_builtin_types(key, owner)),
                Box::new(self.resolve_shadowed_builtin_types(value, owner)),
            ),
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| self.resolve_shadowed_builtin_types(element, owner))
                    .collect(),
            ),
            Type::Proc(parameters, result) => Type::Proc(
                parameters
                    .iter()
                    .map(|parameter| self.resolve_shadowed_builtin_types(parameter, owner))
                    .collect(),
                Box::new(self.resolve_shadowed_builtin_types(result, owner)),
            ),
            Type::Named(name, arguments) => self.resolve_type_names(
                &Type::Named(
                    name.clone(),
                    arguments
                        .iter()
                        .map(|argument| self.resolve_shadowed_builtin_types(argument, owner))
                        .collect(),
                ),
                owner,
            ),
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|member| self.resolve_shadowed_builtin_types(member, owner)),
            ),
            Type::Intersection(members) => Type::intersection(
                members
                    .iter()
                    .map(|member| self.resolve_shadowed_builtin_types(member, owner)),
            ),
            other => other.clone(),
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
        let absolute = prism::text(self.source, &path.as_node())
            .trim_start()
            .starts_with("::");
        let name = path.name().map_or_else(String::new, prism::constant_name);
        let name = match path.parent() {
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
        };
        if absolute {
            format!("::{name}")
        } else {
            name
        }
    }

    fn numeric_sum_type(element: &Type, initial: Option<&Type>) -> Type {
        let mut saw_float = false;
        for type_ in [Some(element), initial].into_iter().flatten() {
            let mut pending = vec![type_];
            while let Some(type_) = pending.pop() {
                match type_ {
                    Type::Integer => {}
                    Type::Float => saw_float = true,
                    Type::Union(members) => pending.extend(members),
                    Type::Never => {}
                    _ => return Type::Any,
                }
            }
        }
        if saw_float {
            Type::Float
        } else {
            Type::Integer
        }
    }

    fn array_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => element.as_ref().clone(),
            Type::Tuple(elements) => {
                let element = elements
                    .iter()
                    .fold(Type::Never, |current, element| current.join(element));
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
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

    fn flattened_array_element_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::Array(element) => self.flattened_array_element_type(element),
            Type::Tuple(elements) => {
                let element = elements.iter().fold(Type::Never, |current, element| {
                    current.join(&self.flattened_array_element_type(element))
                });
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            Type::Union(members) => {
                let element = members.iter().fold(Type::Never, |current, member| {
                    current.join(&self.flattened_array_element_type(member))
                });
                if element.is_never() {
                    Type::Any
                } else {
                    element
                }
            }
            other => other.clone(),
        }
    }
}
