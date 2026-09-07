use crate::diagnostic::{Diagnostic, Severity};
use crate::directives::{effective_typed_mode, is_typed_ignore, typed_mode, TypedMode};
use crate::hir;
use crate::prism;
use crate::signature::{self, AnnotationTable, AssertionKind, MethodSig};
use crate::types::{Type, TypeLattice};
use ruby_prism::{
    ArgumentsNode, CallNode, DefNode, IfNode, Node, ParametersNode, UnlessNode, Visit,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

mod arguments;
mod blocks;
mod builtins;
mod calls;
mod declarations;
mod dispatch;
mod fixpoint;
mod flow;
mod type_resolution;
mod type_system;

use declarations::{DeclarationState, MethodRegistrar};
use fixpoint::FixpointState;
use flow::{Eval, Flow, FlowKind, OutcomeTypes};

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

fn nominal_name(name: &str) -> &str {
    name.strip_prefix("T::").unwrap_or(name)
}

#[derive(Clone, Debug, Default)]
struct ParameterShape {
    parameter_kinds: Vec<(String, signature::ParameterKind)>,
    required_positional: usize,
    accepts_rest: bool,
    rest_index: Option<usize>,
    keywords: BTreeMap<String, bool>,
    accepts_keyword_rest: bool,
    has_block: bool,
    block_name: Option<String>,
}

impl ParameterShape {
    fn from_parameters<'node>(source: &[u8], parameters: Option<ParametersNode<'node>>) -> Self {
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
        let mut parameter_kinds = Vec::new();
        let parameter_name = |parameter: &Node<'_>| {
            parameter
                .as_required_parameter_node()
                .map(|parameter| prism::constant_name(parameter.name()))
                .or_else(|| {
                    parameter
                        .as_optional_parameter_node()
                        .map(|parameter| prism::constant_name(parameter.name()))
                })
                .unwrap_or_else(|| prism::text(source, parameter))
        };
        for parameter in &parameters.requireds() {
            parameter_kinds.push((
                parameter_name(&parameter),
                signature::ParameterKind::Positional,
            ));
        }
        for parameter in &parameters.optionals() {
            parameter_kinds.push((
                parameter_name(&parameter),
                signature::ParameterKind::OptionalPositional,
            ));
        }
        if let Some(rest) = parameters
            .rest()
            .and_then(|node| node.as_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                parameter_kinds.push((
                    prism::constant_name(name),
                    signature::ParameterKind::RestPositional,
                ));
            }
        }
        for parameter in &parameters.posts() {
            parameter_kinds.push((
                parameter_name(&parameter),
                signature::ParameterKind::Positional,
            ));
        }
        for parameter in &parameters.keywords() {
            if let Some(required) = parameter.as_required_keyword_parameter_node() {
                keywords.insert(prism::constant_name(required.name()), true);
                parameter_kinds.push((
                    prism::constant_name(required.name()),
                    signature::ParameterKind::Keyword,
                ));
            } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                keywords.insert(prism::constant_name(optional.name()), false);
                parameter_kinds.push((
                    prism::constant_name(optional.name()),
                    signature::ParameterKind::OptionalKeyword,
                ));
            }
        }
        if let Some(rest) = parameters
            .keyword_rest()
            .and_then(|node| node.as_keyword_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                parameter_kinds.push((
                    prism::constant_name(name),
                    signature::ParameterKind::RestKeyword,
                ));
            }
        }
        if let Some(block) = parameters.block() {
            if let Some(name) = block.name() {
                parameter_kinds.push((prism::constant_name(name), signature::ParameterKind::Block));
            }
        }
        Self {
            parameter_kinds,
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
            shape.has_block && (name == "&" || shape.block_name.as_deref() == Some(name.as_str()));
        if is_block_parameter {
            if optional_proc_type(type_).is_some() {
                // Preserve nilability here. It distinguishes Ruby's
                // optional `&blk` parameters from Sorbet's required block
                // parameters when constructor calls are checked.
                block = Some(type_.clone());
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
        Type::Proc(_, _) | Type::BoundProc { .. } => Some(type_.clone()),
        Type::Union(members)
            if members.iter().all(|member| {
                member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
            }) =>
        {
            members.iter().find_map(|member| {
                matches!(member, Type::Proc(_, _) | Type::BoundProc { .. }).then(|| member.clone())
            })
        }
        _ => None,
    }
}

fn proc_parts(type_: &Type) -> Option<(&[Type], &Type)> {
    match type_ {
        Type::Proc(parameters, result) => Some((parameters, result)),
        Type::BoundProc {
            parameters, result, ..
        } => Some((parameters, result)),
        _ => None,
    }
}

fn proc_arity_narrowing(type_: &Type, arity: usize) -> Option<Type> {
    match type_ {
        Type::Proc(_, result) => Some(Type::Proc(vec![Type::Any; arity], result.clone())),
        Type::BoundProc {
            receiver, result, ..
        } => Some(Type::BoundProc {
            receiver: receiver.clone(),
            parameters: vec![Type::Any; arity],
            result: result.clone(),
        }),
        Type::Union(members) => {
            let narrowed = members
                .iter()
                .filter_map(|member| proc_arity_narrowing(member, arity))
                .collect::<Vec<_>>();
            (!narrowed.is_empty()).then(|| Type::union(narrowed))
        }
        _ => None,
    }
}

fn proc_receiver(type_: &Type) -> Option<&Type> {
    match type_ {
        Type::BoundProc { receiver, .. } => Some(receiver),
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
        parameter_kinds: Vec::new(),
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
        is_abstract: signatures.iter().all(|signature| signature.is_abstract),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Visibility {
    Public,
    Private,
    Protected,
}

fn attribute_writer_signature(signature: &MethodSig) -> MethodSig {
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
    StructField(String, String),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GenericMember {
    index: usize,
    fixed: Option<Type>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ClassInfo {
    is_module: bool,
    extend_self: bool,
    attached_class_member: Option<usize>,
    superclass: Option<String>,
    struct_fields: Option<Vec<String>>,
    includes: Vec<String>,
    prepends: Vec<String>,
    extends: Vec<String>,
    class_methods: Vec<String>,
    requires_ancestors: Vec<String>,
    type_members: BTreeMap<String, GenericMember>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PredicateAlias {
    source: String,
    negated: bool,
    expected: Option<Type>,
}

#[derive(Default)]
struct LocalWriteCollector {
    names: BTreeSet<String>,
}

impl<'pr> Visit<'pr> for LocalWriteCollector {
    fn visit_local_variable_write_node(&mut self, node: &ruby_prism::LocalVariableWriteNode<'pr>) {
        self.names.insert(prism::constant_name(node.name()));
        ruby_prism::visit_local_variable_write_node(self, node);
    }

    fn visit_local_variable_and_write_node(
        &mut self,
        node: &ruby_prism::LocalVariableAndWriteNode<'pr>,
    ) {
        self.names.insert(prism::constant_name(node.name()));
        ruby_prism::visit_local_variable_and_write_node(self, node);
    }

    fn visit_local_variable_or_write_node(
        &mut self,
        node: &ruby_prism::LocalVariableOrWriteNode<'pr>,
    ) {
        self.names.insert(prism::constant_name(node.name()));
        ruby_prism::visit_local_variable_or_write_node(self, node);
    }

    fn visit_local_variable_operator_write_node(
        &mut self,
        node: &ruby_prism::LocalVariableOperatorWriteNode<'pr>,
    ) {
        self.names.insert(prism::constant_name(node.name()));
        ruby_prism::visit_local_variable_operator_write_node(self, node);
    }
}

/// How much file-mode metadata the checker should use. Typey is intentionally
/// permissive for untyped Ruby, while explicit annotations remain checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strictness {
    Ignore,
    /// Sorbet's `typed: true` mode: report calls to APIs that cannot be
    /// resolved, but do not require every method to have a fully inferred
    /// signature.
    True,
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
        Strictness::True => 1,
        Strictness::Strict => 2,
        Strictness::Strong => 3,
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
    /// Types learned from observed calls to an unsigiled method are useful
    /// for expression inference, but they are not a proof about every future
    /// call. Keep their provenance so control-flow predicates do not treat a
    /// sample argument as exhaustive.
    inferred_locals: BTreeSet<String>,
    provisional_locals: BTreeSet<String>,
    open_array_locals: BTreeSet<String>,
    known_nonempty_arrays: BTreeSet<String>,
    predicate_aliases: BTreeMap<String, PredicateAlias>,
    known_truthiness: BTreeMap<String, bool>,
    self_type: Type,
    method_key: Option<MethodKey>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            locals: BTreeMap::new(),
            inferred_locals: BTreeSet::new(),
            provisional_locals: BTreeSet::new(),
            open_array_locals: BTreeSet::new(),
            known_nonempty_arrays: BTreeSet::new(),
            predicate_aliases: BTreeMap::new(),
            known_truthiness: BTreeMap::new(),
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
        let name = name.into();
        self.open_array_locals.remove(&name);
        self.known_nonempty_arrays.remove(&name);
        self.inferred_locals.remove(&name);
        self.provisional_locals.remove(&name);
        self.locals.insert(name.clone(), type_);
        self.predicate_aliases.remove(&name);
        self.known_truthiness.remove(&name);
    }

    fn mark_inferred(&mut self, name: impl Into<String>) {
        let name = name.into();
        if self.locals.contains_key(&name) {
            self.provisional_locals.remove(&name);
            self.inferred_locals.insert(name);
        }
    }

    fn mark_provisional(&mut self, name: impl Into<String>) {
        let name = name.into();
        if self.locals.contains_key(&name) {
            self.inferred_locals.remove(&name);
            self.provisional_locals.insert(name);
        }
    }

    fn is_inferred(&self, name: &str) -> bool {
        self.inferred_locals.contains(name)
    }

    fn is_provisional(&self, name: &str) -> bool {
        self.provisional_locals.contains(name)
    }

    fn bind_predicate_alias(
        &mut self,
        name: impl Into<String>,
        type_: Type,
        alias: PredicateAlias,
    ) {
        let name = name.into();
        self.open_array_locals.remove(&name);
        self.known_nonempty_arrays.remove(&name);
        self.inferred_locals.remove(&name);
        self.provisional_locals.remove(&name);
        self.locals.insert(name.clone(), type_);
        self.predicate_aliases.insert(name.clone(), alias);
        self.known_truthiness.remove(&name);
    }

    fn predicate_alias(&self, name: &str) -> Option<&PredicateAlias> {
        self.predicate_aliases.get(name)
    }

    fn set_known_truthiness(&mut self, name: impl Into<String>, truthy: bool) {
        self.known_truthiness.insert(name.into(), truthy);
    }

    fn known_truthiness(&self, name: &str) -> Option<bool> {
        self.known_truthiness.get(name).copied()
    }

    fn set_known_nonempty_array(&mut self, name: impl Into<String>, nonempty: bool) {
        let name = name.into();
        if nonempty {
            self.known_nonempty_arrays.insert(name);
        } else {
            self.known_nonempty_arrays.remove(&name);
        }
    }

    fn known_nonempty_array(&self, name: &str) -> bool {
        self.known_nonempty_arrays.contains(name)
    }

    /// Join two control-flow environments using the same type lattice as
    /// expression inference. A local which exists on only one path can be
    /// `nil` when the other path is taken.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let lattice = TypeLattice;
        let mut result = Self {
            locals: BTreeMap::new(),
            inferred_locals: self
                .inferred_locals
                .union(&other.inferred_locals)
                .cloned()
                .collect(),
            provisional_locals: self
                .provisional_locals
                .union(&other.provisional_locals)
                .cloned()
                .collect(),
            open_array_locals: self
                .open_array_locals
                .intersection(&other.open_array_locals)
                .cloned()
                .collect(),
            known_nonempty_arrays: self
                .known_nonempty_arrays
                .intersection(&other.known_nonempty_arrays)
                .cloned()
                .collect(),
            predicate_aliases: self
                .predicate_aliases
                .iter()
                .filter_map(|(name, alias)| {
                    (other.predicate_aliases.get(name) == Some(alias))
                        .then(|| (name.clone(), alias.clone()))
                })
                .collect(),
            known_truthiness: self
                .known_truthiness
                .iter()
                .filter_map(|(name, truthy)| {
                    (other.known_truthiness.get(name) == Some(truthy))
                        .then(|| (name.clone(), *truthy))
                })
                .collect(),
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

struct CallSite<'a, 'node> {
    argument_nodes: &'a [Node<'node>],
    argument_types: &'a [Type],
    block: Option<&'a Node<'node>>,
}

pub(super) enum CallArgumentInput<'node> {
    Forwarded {
        node: Node<'node>,
    },
    Positional {
        node: Node<'node>,
    },
    Splat {
        node: Node<'node>,
        expression: Option<Node<'node>>,
    },
    KeywordHash {
        node: Node<'node>,
        entries: Vec<KeywordArgumentInput<'node>>,
    },
}

pub(super) enum KeywordArgumentInput<'node> {
    Pair {
        key: Node<'node>,
        value: Node<'node>,
        name: Option<String>,
    },
    Splat(Option<Node<'node>>),
    Forwarded,
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
    binds_block_to_receiver: bool,
    required_keywords: BTreeSet<String>,
    return_type: Option<Type>,
    return_terminates: bool,
    required_params: usize,
    accepts_rest: bool,
    accepts_keyword_rest: bool,
    is_void: bool,
    is_abstract: bool,
    visibility: Visibility,
    explicit: bool,
    overloads: Vec<MethodSig>,
}

impl MethodState {
    fn explicit_overloads(signatures: &[MethodSig]) -> Self {
        let signature = merge_method_signatures(signatures);
        let (yield_params, block_return_type) = signature
            .block
            .as_ref()
            .and_then(|block| {
                proc_parts(block).map(|(parameters, return_type)| {
                    (
                        parameters.iter().cloned().map(Some).collect(),
                        Some(return_type.clone()),
                    )
                })
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
            binds_block_to_receiver: false,
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
            is_abstract: signature.is_abstract,
            visibility: Visibility::Public,
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
                binds_block_to_receiver: false,
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
                is_abstract: false,
                visibility: Visibility::Public,
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
            binds_block_to_receiver: false,
            required_keywords,
            return_type: None,
            return_terminates: false,
            required_params,
            accepts_rest: false,
            accepts_keyword_rest: false,
            is_void: false,
            is_abstract: false,
            visibility: Visibility::Public,
            explicit: false,
            overloads: Vec::new(),
        }
    }

    fn inferred_accessor(kind: AccessorKind) -> Self {
        let mut state = Self::inferred(None);
        state.return_type = Some(Type::Any);
        state.binds_block_to_receiver = false;
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
            parameter_kinds: Vec::new(),
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
            is_abstract: self.is_abstract,
        }
    }

    fn call_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            parameter_kinds: Vec::new(),
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
            is_abstract: self.is_abstract,
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
        if let Some(block) = &self.block {
            if let Some((parameters, _)) = proc_parts(block) {
                return parameters.to_vec();
            }
        }
        self.yield_params
            .iter()
            .map(|type_| type_.clone().unwrap_or(Type::Any))
            .collect()
    }

    fn block_result_type(&self) -> Type {
        self.block
            .as_ref()
            .and_then(|block| proc_parts(block).map(|(_, result)| result.clone()))
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
    let hir_program = hir::lower(hir::FileId(0), bytes);
    let mut hir_call_ids = HashMap::new();
    let mut hir_assignment_ids = HashMap::new();
    for (index, expression) in hir_program.expressions.iter().enumerate() {
        let span = (expression.span.start as usize, expression.span.end as usize);
        match &expression.kind {
            hir::ExprKind::Call(_) => {
                hir_call_ids
                    .entry(span)
                    .or_insert(hir::ExprId(index as u32));
            }
            hir::ExprKind::Assign { .. } => {
                hir_assignment_ids
                    .entry(span)
                    .or_insert(hir::ExprId(index as u32));
            }
            _ => {}
        }
    }
    let annotations = signature::collect_for_ast(source, &root);
    let mut diagnostics = parsed
        .errors()
        .map(|error| {
            let location = error.location();
            let (start, end) = prism::location_span(&location);
            Diagnostic::error(bytes, error.message(), start, end)
        })
        .collect::<Vec<_>>();
    diagnostics.extend(
        annotations
            .signature_errors
            .iter()
            .map(|error| Diagnostic::error(bytes, &error.message, error.start, error.end)),
    );
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
        hir_program,
        hir_call_ids,
        hir_assignment_ids,
        line_map: prism::LineMap::new(bytes),
        has_inline_assertions: !annotations.assertions.is_empty(),
        annotations,
        config,
        declarations: DeclarationState::default(),
        method_resolution_cache: RefCell::new(BTreeMap::new()),
        global_name_cache: RefCell::new(HashMap::new()),
        instance_self_type_cache: RefCell::new(HashMap::new()),
        ivars: BTreeMap::new(),
        provisional_ivars: BTreeSet::new(),
        class_vars: BTreeMap::new(),
        globals: BTreeMap::new(),
        report: true,
        seed_calls: false,
        rbi_ranges: rbi_ranges.to_vec(),
        builtin_rbi_ranges: builtin_rbi_ranges.to_vec(),
        strictness_ranges: strictness_ranges.to_vec(),
        filter_method_bodies: false,
        fixpoint: FixpointState::default(),
        defer_inline_assertions: false,
        preserve_literal_tuples: false,
        preserve_nested_literal_tuples: false,
        literal_tuple_depth: 0,
        expected_return_type: None,
        substitution_context: None,
        checking_initializer: false,
        initializer_has_block: false,
        initializer_requires_block: false,
        diagnostics: diagnostics.clone(),
        types: Vec::new(),
        untyped_origins: BTreeMap::new(),
        suppress_diagnostics: false,
    };
    let result = analyzer.run(&root);
    (result, diagnostics)
}

fn source_strictness_ranges(source: &str) -> Vec<(usize, usize, Strictness)> {
    let strictness = match effective_typed_mode(source) {
        TypedMode::True => Strictness::True,
        TypedMode::Strict => Strictness::Strict,
        TypedMode::Strong => Strictness::Strong,
        TypedMode::False | TypedMode::Ignore => return Vec::new(),
    };
    vec![(0, source.len(), strictness)]
}

struct Analyzer<'src> {
    source: &'src [u8],
    hir_program: hir::Program,
    hir_call_ids: HashMap<(usize, usize), hir::ExprId>,
    hir_assignment_ids: HashMap<(usize, usize), hir::ExprId>,
    line_map: prism::LineMap,
    has_inline_assertions: bool,
    annotations: AnnotationTable,
    config: CheckerConfig,
    declarations: DeclarationState,
    method_resolution_cache: RefCell<BTreeMap<MethodKey, Option<MethodKey>>>,
    global_name_cache: RefCell<HashMap<String, String>>,
    instance_self_type_cache: RefCell<HashMap<String, Type>>,
    ivars: BTreeMap<IvarKey, Type>,
    provisional_ivars: BTreeSet<IvarKey>,
    class_vars: BTreeMap<ClassVarKey, Type>,
    globals: BTreeMap<String, Type>,
    report: bool,
    seed_calls: bool,
    rbi_ranges: Vec<(usize, usize)>,
    builtin_rbi_ranges: Vec<(usize, usize)>,
    strictness_ranges: Vec<(usize, usize, Strictness)>,
    filter_method_bodies: bool,
    fixpoint: FixpointState,
    defer_inline_assertions: bool,
    preserve_literal_tuples: bool,
    preserve_nested_literal_tuples: bool,
    literal_tuple_depth: usize,
    expected_return_type: Option<Type>,
    substitution_context: Option<MethodKey>,
    checking_initializer: bool,
    initializer_has_block: bool,
    initializer_requires_block: bool,
    diagnostics: Vec<Diagnostic>,
    types: Vec<InferredType>,
    untyped_origins: BTreeMap<(usize, usize), UntypedOrigin>,
    suppress_diagnostics: bool,
}

/// A call shape whose semantic fields come from owned HIR. During this
/// migration the Prism call is retained only as a child-node bridge so the
/// existing evaluator can still evaluate receiver and argument expressions.
/// The evaluator itself never asks the Prism node to decide the call shape.
pub(super) struct HirCallView<'node> {
    pub(super) call: hir::Call,
    prism_call: CallNode<'node>,
}

pub(super) trait CallShape<'node> {
    fn name(&self) -> String;
    fn argument_inputs(&self) -> Vec<CallArgumentInput<'node>>;
    fn receiver(&self) -> Option<Node<'node>>;
    fn block(&self) -> Option<Node<'node>>;
    fn is_safe_navigation(&self) -> bool;
}

impl<'node> CallShape<'node> for CallNode<'node> {
    fn name(&self) -> String {
        prism::constant_name(self.name())
    }

    fn argument_inputs(&self) -> Vec<CallArgumentInput<'node>> {
        prism_call_argument_inputs(self.arguments())
    }

    fn receiver(&self) -> Option<Node<'node>> {
        self.receiver()
    }

    fn block(&self) -> Option<Node<'node>> {
        self.block()
    }

    fn is_safe_navigation(&self) -> bool {
        self.is_safe_navigation()
    }
}

impl<'node> CallShape<'node> for HirCallView<'node> {
    fn name(&self) -> String {
        self.call.name.as_str().to_owned()
    }

    fn argument_inputs(&self) -> Vec<CallArgumentInput<'node>> {
        hir_call_argument_inputs(&self.call.arguments, self.prism_call.arguments())
    }

    fn receiver(&self) -> Option<Node<'node>> {
        self.prism_call.receiver()
    }

    fn block(&self) -> Option<Node<'node>> {
        self.prism_call.block()
    }

    fn is_safe_navigation(&self) -> bool {
        self.call.safe_navigation
    }
}

fn prism_call_argument_inputs<'node>(
    arguments: Option<ArgumentsNode<'node>>,
) -> Vec<CallArgumentInput<'node>> {
    arguments.map_or_else(Vec::new, |arguments| {
        prism_argument_inputs_from_nodes(arguments.arguments().into_iter().collect())
    })
}

fn prism_argument_inputs_from_nodes<'node>(
    arguments: Vec<Node<'node>>,
) -> Vec<CallArgumentInput<'node>> {
    arguments
        .into_iter()
        .map(|argument| {
            if argument.as_forwarding_arguments_node().is_some() {
                return CallArgumentInput::Forwarded { node: argument };
            }
            if let Some(splat) = argument.as_splat_node() {
                return CallArgumentInput::Splat {
                    node: argument,
                    expression: splat.expression(),
                };
            }
            if let Some(keyword_hash) = argument.as_keyword_hash_node() {
                let entries = keyword_hash
                    .elements()
                    .into_iter()
                    .map(|child| {
                        if let Some(assoc) = child.as_assoc_node() {
                            let key = assoc.key();
                            let name = key.as_symbol_node().map(|symbol| {
                                String::from_utf8_lossy(symbol.unescaped()).into_owned()
                            });
                            KeywordArgumentInput::Pair {
                                key,
                                value: assoc.value(),
                                name,
                            }
                        } else if let Some(splat) = child.as_assoc_splat_node() {
                            splat
                                .value()
                                .map_or(KeywordArgumentInput::Forwarded, |value| {
                                    KeywordArgumentInput::Splat(Some(value))
                                })
                        } else {
                            KeywordArgumentInput::Forwarded
                        }
                    })
                    .collect();
                return CallArgumentInput::KeywordHash {
                    node: argument,
                    entries,
                };
            }
            CallArgumentInput::Positional { node: argument }
        })
        .collect()
}

fn hir_call_argument_inputs<'node>(
    arguments: &[hir::Argument],
    prism_arguments: Option<ArgumentsNode<'node>>,
) -> Vec<CallArgumentInput<'node>> {
    let raw = prism_call_argument_inputs(prism_arguments);
    let mut hir_index = 0;
    let mut result = Vec::with_capacity(raw.len());
    for input in raw {
        match input {
            CallArgumentInput::KeywordHash { node, entries } => {
                let mut entries = entries.into_iter();
                let mut hir_entries = Vec::new();
                while let Some(argument) = arguments.get(hir_index) {
                    match argument {
                        hir::Argument::Keyword { name, .. } => {
                            let Some(KeywordArgumentInput::Pair { key, value, .. }) =
                                entries.next()
                            else {
                                break;
                            };
                            hir_entries.push(KeywordArgumentInput::Pair {
                                key,
                                value,
                                name: Some(name.as_str().to_owned()),
                            });
                            hir_index += 1;
                        }
                        hir::Argument::KeywordSplat(_) => {
                            let Some(KeywordArgumentInput::Splat(value)) = entries.next() else {
                                break;
                            };
                            hir_entries.push(KeywordArgumentInput::Splat(value));
                            hir_index += 1;
                        }
                        hir::Argument::Forwarded => {
                            let Some(KeywordArgumentInput::Forwarded) = entries.next() else {
                                break;
                            };
                            hir_entries.push(KeywordArgumentInput::Forwarded);
                            hir_index += 1;
                        }
                        _ => break,
                    }
                }
                result.push(CallArgumentInput::KeywordHash {
                    node,
                    entries: hir_entries,
                });
            }
            CallArgumentInput::Forwarded { node } => {
                if matches!(arguments.get(hir_index), Some(hir::Argument::Forwarded)) {
                    hir_index += 1;
                }
                result.push(CallArgumentInput::Forwarded { node });
            }
            CallArgumentInput::Splat { node, expression } => {
                if matches!(arguments.get(hir_index), Some(hir::Argument::Splat(_))) {
                    hir_index += 1;
                }
                result.push(CallArgumentInput::Splat { node, expression });
            }
            CallArgumentInput::Positional { node } => {
                if matches!(arguments.get(hir_index), Some(hir::Argument::Positional(_))) {
                    hir_index += 1;
                }
                result.push(CallArgumentInput::Positional { node });
            }
        }
    }
    result
}

impl<'src> Analyzer<'src> {
    fn hir_call_view<'node>(
        &self,
        node: &Node<'_>,
        prism_call: CallNode<'node>,
    ) -> Option<HirCallView<'node>> {
        let span = prism::span(node);
        let expression_id = self.hir_call_ids.get(&span)?;
        let hir::ExprKind::Call(call) = &self
            .hir_program
            .expressions
            .get(expression_id.0 as usize)?
            .kind
        else {
            return None;
        };
        Some(HirCallView {
            call: call.clone(),
            prism_call,
        })
    }

    fn hir_assignment_for_node(
        &self,
        node: &Node<'_>,
    ) -> Option<(hir::AssignTarget, hir::ExprId, hir::AssignOperator)> {
        let expression_id = self.hir_assignment_ids.get(&prism::span(node))?;
        let hir::ExprKind::Assign {
            target,
            value,
            operator,
            ..
        } = &self
            .hir_program
            .expressions
            .get(expression_id.0 as usize)?
            .kind
        else {
            return None;
        };
        Some((target.clone(), *value, operator.clone()))
    }

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

    fn record_inferred_return(&mut self, key: MethodKey, actual: Type, terminates: bool) {
        match self.fixpoint.pending_returns.entry(key) {
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
        let pending_returns = std::mem::take(&mut self.fixpoint.pending_returns);
        for (key, (return_type, return_terminates)) in pending_returns {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit {
                    let changed = state.return_type.as_ref() != Some(&return_type)
                        || state.return_terminates != return_terminates;
                    state.return_type = Some(return_type);
                    state.return_terminates = return_terminates;
                    if changed {
                        self.fixpoint.changed_methods.insert(key);
                    }
                }
            }
        }
    }

    fn run<'node>(mut self, root: &Node<'node>) -> CheckResult {
        let run_started = std::time::Instant::now();
        if self.config.debug {
            eprintln!("[typey] registering declarations");
        }
        self.register_methods(root);
        let parse_diagnostics = std::mem::take(&mut self.diagnostics);
        if self.config.debug {
            eprintln!(
                "[typey] registered {} methods, {} classes, and {} type aliases",
                self.declarations.methods.len(),
                self.declarations.classes.len(),
                self.declarations.type_aliases.len()
            );
            eprintln!(
                "[typey] registration complete in {:?}",
                run_started.elapsed()
            );
        }

        // First solve summaries without emitting diagnostics or retaining
        // transient node types. This is the same shape as Spinel's analysis:
        // all definitions are registered, then the tables are refined until
        // one complete pass makes no change.
        self.report = false;
        self.seed_calls = true;
        self.filter_method_bodies = false;
        self.fixpoint.debug_phase = "seed";
        self.fixpoint.debug_round = 0;
        self.types.clear();
        self.fixpoint.debug_nodes = 0;
        if self.config.debug {
            eprintln!("[typey] seeding top-level call sites");
        }
        self.fixpoint.pending_returns.clear();
        self.fixpoint.collecting_returns = true;
        let seed_started = std::time::Instant::now();
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);
        self.fixpoint.collecting_returns = false;
        self.commit_inferred_returns();
        if self.config.debug {
            eprintln!("[typey] seed complete in {:?}", seed_started.elapsed());
        }
        self.seed_calls = false;
        self.fixpoint.changed_methods.clear();
        self.fixpoint.changed_shared.clear();

        let mut pending_methods = self
            .declarations
            .methods
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
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
            self.fixpoint.active_methods = pending_methods.clone();
            self.filter_method_bodies = true;
            self.fixpoint.changed_methods.clear();
            self.fixpoint.changed_shared.clear();
            self.fixpoint.debug_phase = "inference";
            self.fixpoint.debug_round = round;
            self.types.clear();
            self.fixpoint.debug_nodes = 0;
            if self.config.debug {
                eprintln!(
                    "[typey] worklist round {round}: evaluating {} scheduled methods",
                    pending_methods.len()
                );
            }
            let round_started = std::time::Instant::now();
            // Return summaries are computed synchronously: every method body
            // reads the summaries committed by the previous round, and all
            // candidates from this round are committed together below. This
            // avoids source-order effects when a caller appears before its
            // callee or when conditional branches define the same method.
            self.fixpoint.pending_returns.clear();
            self.fixpoint.collecting_returns = true;
            let mut environment = Environment::default();
            self.eval_node(root, &mut environment);
            self.fixpoint.collecting_returns = false;
            self.commit_inferred_returns();

            let changed_methods = std::mem::take(&mut self.fixpoint.changed_methods);
            let changed_shared = std::mem::take(&mut self.fixpoint.changed_shared);
            let mut next_pending = BTreeSet::new();
            for method in &changed_methods {
                next_pending.insert(method.clone());
                if let Some(callers) = self.fixpoint.method_callers.get(method) {
                    next_pending.extend(callers.iter().cloned());
                }
            }
            for shared_key in &changed_shared {
                if let Some(readers) = self.fixpoint.shared_readers.get(shared_key) {
                    next_pending.extend(readers.iter().cloned());
                }
            }
            if self.config.debug {
                eprintln!(
                    "[typey] worklist round {round} complete: {} changed methods, {} changed shared keys, {} scheduled next",
                    changed_methods.len(),
                    changed_shared.len(),
                    next_pending.len(),
                );
                eprintln!(
                    "[typey] worklist round {round} elapsed {:?}",
                    round_started.elapsed()
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
        self.fixpoint.active_methods.clear();
        self.fixpoint.debug_phase = "final";
        self.fixpoint.debug_round = 0;
        self.fixpoint.debug_nodes = 0;
        if self.config.debug {
            eprintln!("[typey] final reporting pass");
        }
        let final_started = std::time::Instant::now();
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);
        if self.config.debug {
            eprintln!(
                "[typey] final pass complete in {:?}",
                final_started.elapsed()
            );
        }

        self.report_inference_gaps();
        let types = Self::deduplicate_types(std::mem::take(&mut self.types));
        let mut seen_diagnostics = BTreeSet::new();
        self.diagnostics.retain(|diagnostic| {
            seen_diagnostics.insert((
                matches!(diagnostic.severity, Severity::Note),
                diagnostic.start,
                diagnostic.end,
                diagnostic.message.clone(),
            ))
        });
        self.diagnostics.sort_by(|left, right| {
            left.start
                .cmp(&right.start)
                .then_with(|| left.message.cmp(&right.message))
        });
        if self.config.debug {
            eprintln!(
                "[typey] complete: {} diagnostics, {} recorded types in {:?}",
                self.diagnostics.len(),
                types.len(),
                run_started.elapsed()
            );
        }
        CheckResult {
            diagnostics: self.diagnostics,
            types,
        }
    }

    fn report_inference_gaps(&mut self) {
        if self.config.strictness == Strictness::Ignore && self.strictness_ranges.is_empty() {
            return;
        }

        let gaps = self
            .declarations
            .definitions
            .iter()
            .filter_map(|(offset, key)| {
                let strictness = self.strictness_at(*offset);
                if strictness_rank(strictness) < strictness_rank(Strictness::Strict) {
                    return None;
                }
                let state = self.declarations.methods.get(key)?;
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

    fn reports_missing_api<'node>(&self, node: &Node<'node>) -> bool {
        let (start, _) = prism::span(node);
        strictness_rank(self.strictness_at(start)) >= strictness_rank(Strictness::True)
            && !self.is_rbi_definition(node)
    }

    fn report_missing_method_if_needed<'node>(
        &mut self,
        node: &Node<'node>,
        receiver: &Type,
        name: &str,
        resolved: bool,
    ) {
        if resolved
            || !self.reports_missing_api(node)
            || receiver.is_any()
            || receiver.contains_any()
            || receiver.is_never()
            || matches!(receiver, Type::Anything)
        {
            return;
        }
        self.error(
            node,
            format!("Method `{name}` does not exist on `{receiver}`"),
        );
    }

    fn constant_is_known(&self, environment: &Environment, name: &str) -> bool {
        let name = name.trim_start_matches("::");
        if name == "T" || name.starts_with("T::") {
            return true;
        }
        let owner = self.lexical_owner(environment);
        let resolved = self.resolve_name(name, owner.as_deref());
        self.declarations.classes.contains_key(&resolved)
            || self.declarations.constants.contains_key(&resolved)
            || self.declarations.type_aliases.contains_key(&resolved)
            || self.known_nominal_name(name)
            || self.declarations.class_name_suffixes.contains_key(name)
            || self.declarations.constant_name_suffixes.contains_key(name)
    }

    fn report_missing_constant_if_needed<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &Environment,
        name: &str,
    ) {
        if !self.reports_missing_api(node) || self.constant_is_known(environment, name) {
            return;
        }
        self.error(
            node,
            format!(
                "Unable to resolve constant `{}`",
                name.trim_start_matches("::")
            ),
        );
    }

    fn validate_rbs_parameter_kinds(
        &mut self,
        offset: usize,
        ruby_parameters: &[(String, signature::ParameterKind)],
        signature: &MethodSig,
    ) {
        for ((name, ruby_kind), rbs_kind) in ruby_parameters.iter().zip(&signature.parameter_kinds)
        {
            if ruby_kind == rbs_kind {
                continue;
            }
            self.diagnostics.push(Diagnostic::error(
                self.source,
                format!(
                    "Argument kind mismatch for `{name}`, method declares `{}`, but RBS signature declares `{}`",
                    ruby_kind.display_name(),
                    rbs_kind.display_name(),
                ),
                offset,
                offset,
            ));
        }
    }

    fn validate_sorbet_parameter_names(
        &mut self,
        definition_offset: usize,
        signature_offset: usize,
        ruby_parameters: &ParameterShape,
        signature: &MethodSig,
    ) {
        for name in &signature.param_names {
            let matches_definition = ruby_parameters
                .parameter_kinds
                .iter()
                .any(|(defined, _)| defined == name)
                || (name == "&"
                    && ruby_parameters.has_block
                    && ruby_parameters.block_name.is_none());
            if !matches_definition {
                self.diagnostics.push(Diagnostic::error(
                    self.source,
                    format!("Unknown parameter name `{name}`"),
                    signature_offset,
                    signature_offset,
                ));
            }
        }

        if let Some(block_name) = ruby_parameters.block_name.as_deref() {
            if signature.param_names.iter().any(|name| name == "&")
                && !signature.param_names.iter().any(|name| name == block_name)
            {
                self.diagnostics.push(Diagnostic::error(
                    self.source,
                    format!("Malformed `sig`. Type not specified for parameter `{block_name}`"),
                    definition_offset,
                    definition_offset,
                ));
            }
        }
    }

    fn register_methods<'node>(&mut self, root: &Node<'node>) {
        self.declarations.methods.clear();
        self.declarations.type_aliases = self.annotations.type_aliases.clone();
        let mut registrar = MethodRegistrar::new(
            self.source,
            &mut self.diagnostics,
            &mut self.declarations,
            &self.annotations.attribute_annotations,
            &self.annotations.class_type_parameters,
        );
        registrar.visit(root);
        self.normalize_class_graph();

        // `class Result < Struct.new(:status, :message)` creates a concrete
        // struct subclass with a generated initializer. Keep the generated
        // constructor and fields in the workspace graph just as for
        // `Result = Struct.new(...)`.
        let struct_subclasses = self
            .declarations
            .classes
            .iter()
            .filter_map(|(owner, info)| {
                info.struct_fields
                    .as_ref()
                    .map(|fields| (owner.clone(), fields.clone()))
            })
            .collect::<Vec<_>>();
        for (owner, fields) in struct_subclasses {
            self.declarations
                .struct_fields
                .insert(owner.clone(), fields.clone());
            for field in &fields {
                let reader = MethodKey {
                    owner: Some(owner.clone()),
                    name: field.clone(),
                    singleton: false,
                };
                self.declarations
                    .accessors
                    .entry(reader.clone())
                    .or_insert(AccessorKind::Reader);
                self.declarations
                    .methods
                    .entry(reader)
                    .or_insert_with(|| MethodState::inferred_accessor(AccessorKind::Reader));

                let writer = MethodKey {
                    owner: Some(owner.clone()),
                    name: format!("{field}="),
                    singleton: false,
                };
                self.declarations
                    .accessors
                    .entry(writer.clone())
                    .or_insert(AccessorKind::Writer);
                self.declarations
                    .methods
                    .entry(writer)
                    .or_insert_with(|| MethodState::inferred_accessor(AccessorKind::Writer));
            }
            let key = MethodKey {
                owner: Some(owner),
                name: "initialize".to_owned(),
                singleton: false,
            };
            self.declarations.methods.entry(key).or_insert_with(|| {
                let mut state = MethodState::inferred(None);
                state.params = vec![Some(Type::Any); fields.len()];
                state.required_params = fields.len();
                state.return_type = Some(Type::Nil);
                state
            });
        }

        // Attribute annotations are registered while walking the AST, before
        // the analyzer has its final class table. Resolve their relative
        // names just like method annotations once all declarations are known.
        let accessor_keys = self
            .declarations
            .accessors
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for key in accessor_keys {
            let Some(signatures) = self
                .declarations
                .methods
                .get(&key)
                .filter(|state| state.explicit)
                .map(|state| state.overloads.clone())
            else {
                continue;
            };
            let signatures = signatures
                .iter()
                .map(|signature| self.resolve_signature_names(signature, key.owner.as_deref()))
                .collect::<Vec<_>>();
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                *state = MethodState::explicit_overloads(&signatures);
            }
        }

        // Resolve annotation offsets through the same definition table used by
        // body evaluation. This makes signatures owner-aware and prevents a
        // method called `remove` (or `initialize`) in one file from changing a
        // same-named method elsewhere in a workspace.
        let mut source_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let mut rbi_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let mut builtin_rbi_signatures = BTreeMap::<MethodKey, Vec<MethodSig>>::new();
        let method_annotations = self.annotations.method_annotations.clone();
        let method_annotation_spans = self.annotations.method_annotation_spans.clone();
        for (offset, signatures) in &method_annotations {
            let Some(key) = self.declarations.definitions.get(offset).cloned() else {
                continue;
            };
            let raw_signatures = signatures.clone();
            let signatures = signatures
                .iter()
                .map(|signature| {
                    let signature = self.declarations.parameter_shapes.get(offset).map_or_else(
                        || signature.clone(),
                        |shape| apply_parameter_shape(signature, shape),
                    );
                    self.resolve_signature_names(&signature, key.owner.as_deref())
                })
                .collect::<Vec<_>>();
            let ruby_parameter_kinds = self
                .declarations
                .parameter_shapes
                .get(offset)
                .map(|shape| shape.parameter_kinds.clone());
            let is_source_annotation = !self
                .rbi_ranges
                .iter()
                .chain(&self.builtin_rbi_ranges)
                .any(|(start, end)| *offset >= *start && *offset < *end);
            if is_source_annotation {
                if let Some(ruby_parameter_kinds) = ruby_parameter_kinds.as_deref() {
                    for signature in &signatures {
                        if !signature.parameter_kinds.is_empty() {
                            self.validate_rbs_parameter_kinds(
                                *offset,
                                ruby_parameter_kinds,
                                signature,
                            );
                        }
                    }
                }
                if let Some(shape) = self.declarations.parameter_shapes.get(offset).cloned() {
                    for (index, signature) in raw_signatures.iter().enumerate() {
                        if !signature.param_names.is_empty() {
                            let signature_offset = method_annotation_spans
                                .get(offset)
                                .and_then(|spans| spans.get(index))
                                .map_or(*offset, |(start, _)| *start);
                            self.validate_sorbet_parameter_names(
                                *offset,
                                signature_offset,
                                &shape,
                                signature,
                            );
                        }
                    }
                }
            }
            if is_source_annotation {
                for (index, signature) in signatures.iter().enumerate() {
                    let signature_offset = method_annotation_spans
                        .get(offset)
                        .and_then(|spans| spans.get(index))
                        .map_or(*offset, |(start, _)| *start);
                    self.validate_attached_class_signature(signature_offset, &key, signature);
                }
            }
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
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit {
                    *state = MethodState::explicit_overloads(&signatures);
                }
            }
        }
        for (key, signatures) in builtin_rbi_signatures {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit {
                    *state = MethodState::explicit_overloads(&signatures);
                }
            }
        }

        // An RBI declaration without a signature is an external method, not
        // a method whose return type is known to be bottom. `MethodState`
        // uses `None`/`Never` provisionally for unresolved source methods so
        // convergence can fill them in later, but an empty RBI body has no
        // implementation for the worklist to analyze. Seed those declarations
        // with Sorbet's gradual fallback instead of leaking `T.noreturn` into
        // callers and making ordinary branches appear unreachable.
        let rbi_definition_keys = self
            .declarations
            .definitions
            .iter()
            .filter(|(offset, _)| self.is_rbi_offset(**offset))
            .map(|(_, key)| key.clone())
            .collect::<BTreeSet<_>>();
        for key in rbi_definition_keys {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit && state.return_type.is_none() {
                    state.return_type = Some(Type::Any);
                }
            }
        }

        self.rebuild_nominal_name_indexes();
    }

    fn contains_attached_class_type(type_: &Type) -> bool {
        match type_ {
            Type::AttachedClass | Type::AttachedClassOf(_) => true,
            Type::Named(_, arguments) => arguments.iter().any(Self::contains_attached_class_type),
            Type::Array(element) => Self::contains_attached_class_type(element),
            Type::Hash(key, value) => {
                Self::contains_attached_class_type(key) || Self::contains_attached_class_type(value)
            }
            Type::Tuple(elements) | Type::Union(elements) | Type::Intersection(elements) => {
                elements.iter().any(Self::contains_attached_class_type)
            }
            Type::Proc(parameters, result) => {
                parameters.iter().any(Self::contains_attached_class_type)
                    || Self::contains_attached_class_type(result)
            }
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => {
                Self::contains_attached_class_type(receiver)
                    || parameters.iter().any(Self::contains_attached_class_type)
                    || Self::contains_attached_class_type(result)
            }
            _ => false,
        }
    }

    fn attached_class_context_is_valid(&self, key: &MethodKey) -> bool {
        let Some(owner) = key.owner.as_deref() else {
            return false;
        };
        let Some(info) = self.declarations.classes.get(owner) else {
            return false;
        };
        (key.singleton && !info.is_module)
            || (!key.singleton && info.is_module && info.attached_class_member.is_some())
    }

    fn validate_attached_class_signature(
        &mut self,
        offset: usize,
        key: &MethodKey,
        signature: &MethodSig,
    ) {
        let has_in_parameters = signature
            .params
            .iter()
            .any(Self::contains_attached_class_type)
            || signature
                .keywords
                .values()
                .any(|parameter| Self::contains_attached_class_type(&parameter.type_));
        let has_in_return = Self::contains_attached_class_type(&signature.return_type);
        let has_in_block = signature
            .block
            .as_ref()
            .is_some_and(Self::contains_attached_class_type);
        if !has_in_parameters && !has_in_return && !has_in_block {
            return;
        }

        let owner = key.owner.as_deref().unwrap_or("the module");
        let info = self.declarations.classes.get(owner);
        let is_module = info.is_some_and(|info| info.is_module);
        let has_attached_class = info.is_some_and(|info| info.attached_class_member.is_some());
        let message = if key.singleton && is_module {
            Some(
                "`T.attached_class` cannot be used in singleton methods on modules, because modules cannot be instantiated"
                    .to_owned(),
            )
        } else if !key.singleton && is_module && !has_attached_class {
            Some(format!(
                "`{owner}` must declare `has_attached_class!` before module instance methods can use `T.attached_class`"
            ))
        } else if !key.singleton && !is_module {
            Some(
                "`T.attached_class` may only be used in singleton methods on classes or instance methods on `has_attached_class!` modules"
                    .to_owned(),
            )
        } else if has_in_parameters {
            Some("`T.attached_class` may only be used in an `:out` context".to_owned())
        } else {
            None
        };
        let Some(message) = message else {
            return;
        };
        // The signature span is already the source location of the `sig`
        // call. Do not search backwards for the type text: upstream fixtures
        // place expectation comments between the signature and definition,
        // and that search can accidentally select `T.attached_class` from a
        // prose comment instead of the declaration being validated.
        let start = offset.min(self.source.len());
        let end = self
            .source
            .get(start..)
            .and_then(|source| source.iter().position(|byte| *byte == b'\n'))
            .map_or(self.source.len(), |line_end| start + line_end);
        self.diagnostics
            .push(Diagnostic::error(self.source, message, start, end));
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
            is_send: self.report && Self::is_send_node(node),
        });
        type_
    }

    fn deduplicate_types(types: Vec<InferredType>) -> Vec<InferredType> {
        let mut by_span = BTreeMap::<(usize, usize), InferredType>::new();
        for inferred in types {
            let key = (inferred.start, inferred.end);
            if let Some(previous) = by_span.get_mut(&key) {
                let is_send = previous.is_send || inferred.is_send;
                match (previous.type_.contains_any(), inferred.type_.contains_any()) {
                    (true, false) => *previous = inferred,
                    (false, true) => {}
                    (false, false) => {
                        previous.type_ = previous.type_.join(&inferred.type_);
                        previous.untyped_origin = None;
                    }
                    (true, true) => *previous = inferred,
                }
                previous.is_send = is_send;
            } else {
                by_span.insert(key, inferred);
            }
        }
        by_span.into_values().collect()
    }

    fn error<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.report || self.suppress_diagnostics {
            return;
        }
        let (start, end) = prism::span(node);
        self.diagnostics.push(Diagnostic::error_with_line_map(
            self.source,
            &self.line_map,
            message,
            start,
            end,
        ));
    }

    fn note<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.report || self.suppress_diagnostics {
            return;
        }
        let (start, end) = prism::span(node);
        self.diagnostics.push(Diagnostic::note_with_line_map(
            self.source,
            &self.line_map,
            message,
            start,
            end,
        ));
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
            Eval::unreachable()
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
            Eval::unreachable()
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
        receiver_node: Option<&Node<'node>>,
        arguments: Option<ruby_prism::ArgumentsNode<'node>>,
        environment: &mut Environment,
    ) -> IndexAccess<'node> {
        let receiver_result = receiver_node.as_ref().map_or_else(
            || Eval::value(Type::Object),
            |receiver| self.eval_node(receiver, environment),
        );
        let argument_inputs = prism_call_argument_inputs(arguments);
        let evaluated = self.evaluate_call_arguments(argument_inputs, environment);
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
        let access = self.eval_index_access(receiver_node.as_ref(), arguments, environment);
        let current = receiver_node
            .as_ref()
            .and_then(|receiver| {
                self.receiver_method_key(Some(receiver), &access.receiver_type, "[]", environment)
            })
            .and_then(|key| {
                self.eval_resolved_receiver_call(
                    node,
                    "[]",
                    &key,
                    &access.receiver_type,
                    &access.arguments,
                    None,
                    environment,
                )
                .map(|(type_, _)| type_)
            })
            .unwrap_or_else(|| {
                let site = CallSite {
                    argument_nodes: &access.arguments.argument_nodes,
                    argument_types: &access.arguments.argument_types,
                    block: None,
                };
                self.eval_method_call(&access.receiver_type, "[]", &site, environment)
            });
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
        if !self.defer_inline_assertions {
            if let Some(assertion) = self.inline_assertion_for_node(node) {
                if assertion.kind == AssertionKind::SelfAs {
                    let previous_self_type = environment.self_type.clone();
                    environment.self_type = self.resolve_type_names(
                        &assertion.type_,
                        self.lexical_owner(environment).as_deref(),
                    );
                    let result = self.eval_node_inner(node, environment);
                    environment.self_type = previous_self_type;
                    return result;
                }
            }
        }
        self.eval_node_inner(node, environment)
    }

    fn eval_node_inner<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if self.config.debug {
            self.fixpoint.debug_nodes += 1;
            if self
                .fixpoint
                .debug_nodes
                .is_multiple_of(DEBUG_NODE_INTERVAL)
            {
                let (start, _) = prism::span(node);
                if self.fixpoint.debug_round == 0 {
                    eprintln!(
                        "[typey] {} pass: visited {} nodes (source offset {})",
                        self.fixpoint.debug_phase, self.fixpoint.debug_nodes, start
                    );
                } else {
                    eprintln!(
                        "[typey] fixpoint round {} {} pass: visited {} nodes (source offset {})",
                        self.fixpoint.debug_round,
                        self.fixpoint.debug_phase,
                        self.fixpoint.debug_nodes,
                        start
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
            if let Some(superclass) = class.superclass() {
                // The registrar models dynamic superclasses such as
                // `Struct.new(...)`, but the expression is still evaluated
                // at runtime and must contribute its send sites and type
                // effects to the final pass.
                let _ = self.eval_node(&superclass, environment);
            }
            if let Some(body) = class.body() {
                let mut class_environment = environment.clone();
                class_environment.self_type = Self::class_object_type(&class_name);
                let class_body_key = MethodKey {
                    owner: Some(class_name),
                    name: "<class-body>".to_owned(),
                    singleton: true,
                };
                class_environment.method_key = Some(class_body_key.clone());
                let previous_substitution_context =
                    self.substitution_context.replace(class_body_key);
                self.eval_node(&body, &mut class_environment);
                self.substitution_context = previous_substitution_context;
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
                let module_body_key = MethodKey {
                    owner: Some(module_name),
                    name: "<module-body>".to_owned(),
                    singleton: true,
                };
                module_environment.method_key = Some(module_body_key.clone());
                let previous_substitution_context =
                    self.substitution_context.replace(module_body_key);
                self.eval_node(&body, &mut module_environment);
                self.substitution_context = previous_substitution_context;
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
                let singleton_body_key = MethodKey {
                    owner,
                    name: "<singleton-body>".to_owned(),
                    singleton: true,
                };
                singleton_environment.method_key = Some(singleton_body_key.clone());
                let previous_substitution_context =
                    self.substitution_context.replace(singleton_body_key);
                self.eval_node(&body, &mut singleton_environment);
                self.substitution_context = previous_substitution_context;
            }
            return Eval::value(self.record(node, Type::Nil));
        }
        if let Some(call) = node.as_call_node() {
            if let Some((target, _, operator)) = self.hir_assignment_for_node(node) {
                if matches!(operator, hir::AssignOperator::Set)
                    && matches!(
                        target,
                        hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. }
                    )
                {
                    return self.eval_hir_set_assignment(node, &call, &target, environment);
                }
            }
            let hir_call = self.hir_call_view(node, call).unwrap_or_else(|| {
                let (start, end) = prism::span(node);
                    panic!(
                        "every ordinary call must have an owned HIR call shape: {}..{} `{}` (HIR expressions: {}, calls: {})",
                        start,
                        end,
                        String::from_utf8_lossy(self.source.get(start..end).unwrap_or_default()),
                        self.hir_program.expressions.len(),
                        self.hir_call_ids.len()
                    )
            });
            return self.eval_call_result(node, &hir_call, environment);
        }
        if let Some(multi) = node.as_multi_write_node() {
            let previous_expected_return = self.expected_return_type.take();
            let previous_preserve_literal_tuples = self.preserve_literal_tuples;
            self.preserve_literal_tuples = true;
            if let Some(array) = multi.value().as_array_node() {
                self.expected_return_type =
                    Some(Type::Tuple(vec![Type::Any; array.elements().len()]));
            }
            let mut result = self.eval_node(&multi.value(), environment);
            self.expected_return_type = previous_expected_return;
            self.preserve_literal_tuples = previous_preserve_literal_tuples;
            if let Some(type_) = result.normal_type.clone() {
                let lefts = multi.lefts().into_iter().collect::<Vec<_>>();
                let rights = multi.rights().into_iter().collect::<Vec<_>>();
                let known_length = multi
                    .value()
                    .as_array_node()
                    .filter(|array| {
                        array
                            .elements()
                            .iter()
                            .all(|element| element.as_splat_node().is_none())
                    })
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
            let struct_type = self.struct_subclass_type(environment, &value, &name);
            if let Some(struct_type) = struct_type.as_ref() {
                self.eval_dynamic_struct_block(&value, struct_type, environment);
            }
            let actual = struct_type.unwrap_or(actual);
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
            let struct_type = self.struct_subclass_type(environment, &value, &name);
            if let Some(struct_type) = struct_type.as_ref() {
                self.eval_dynamic_struct_block(&value, struct_type, environment);
            }
            let actual = struct_type.unwrap_or(actual);
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
            let type_ =
                self.preserve_typed_empty_array_ivar(environment, &name, &value_node, type_);
            let provisional = value_node
                .as_local_variable_read_node()
                .is_some_and(|local| {
                    environment.is_provisional(&prism::constant_name(local.name()))
                });
            self.observe_ivar(environment, name.clone(), &type_, provisional);
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
                self.observe_ivar(environment, name.clone(), type_, false);
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
                self.observe_ivar(environment, name.clone(), type_, false);
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
            self.observe_ivar(environment, name.clone(), &declared, false);
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
            let name = prism::constant_name(write.name());
            if let Some(alias) = self.predicate_alias_for_value(&value_node, environment) {
                environment.bind_predicate_alias(name, type_.clone(), alias);
            } else {
                environment.bind(name, type_.clone());
            }
            if value_node
                .as_array_node()
                .is_some_and(|array| array.elements().is_empty())
                && matches!(&type_, Type::Array(element) if element.is_any())
            {
                environment
                    .open_array_locals
                    .insert(prism::constant_name(write.name()));
            }
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
            self.report_missing_constant_if_needed(node, environment, &name);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if let Some(path) = node.as_constant_path_node() {
            let name = self.constant_path_name(&path);
            let actual = self.constant_type(environment, &name);
            self.report_missing_constant_if_needed(node, environment, &name);
            let type_ = self.apply_inline_assertion(node, actual);
            return Eval::value(self.record(node, type_));
        }
        if node.as_self_node().is_some() {
            let type_ = self.apply_inline_assertion(node, environment.self_type.clone());
            return Eval::value(self.record(node, type_));
        }
        if let Some(defined) = node.as_defined_node() {
            // Sorbet inspects the operand of `defined?` for send accounting
            // and type propagation, but it does not report ordinary missing
            // API errors from that operand: the expression is only queried
            // for whether it could be defined at runtime.
            let previous_suppression = self.suppress_diagnostics;
            self.suppress_diagnostics = true;
            let _ = self.eval_node(&defined.value(), environment);
            self.suppress_diagnostics = previous_suppression;
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
            self.bind_parameters(parameters, Some(&signature), &mut closure_environment, true);
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
            let tuple_depth = self.literal_tuple_depth;
            self.literal_tuple_depth += 1;
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
            self.literal_tuple_depth = tuple_depth;
            let element = if element.is_never() {
                // An empty nested array inside a multi-assignment tuple is
                // a bottom-valued container, not an independently untyped
                // array.  Keeping `Never` here lets a concrete sibling
                // branch refine it during tuple joins without losing the
                // tuple's known component types.
                if (self.preserve_literal_tuples || self.preserve_nested_literal_tuples)
                    && tuple_depth > 0
                {
                    Type::Never
                } else {
                    Type::Any
                }
            } else {
                element
            };
            let inferred = if fixed_length
                && ((self.preserve_literal_tuples && tuple_depth == 0)
                    || (self.preserve_nested_literal_tuples && tuple_depth > 0)
                    || self.expected_return_type.as_ref().is_some_and(|expected| {
                        tuple_depth == 0
                            && matches!(expected, Type::Tuple(elements) if elements.len() == element_types.len())
                    }))
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
            let argument_inputs = prism_call_argument_inputs(yield_node.arguments());
            let evaluated = self.evaluate_call_arguments(argument_inputs, environment);
            let arguments = evaluated.arguments;
            let argument_types = arguments.argument_types.clone();
            let method_key = environment.method_key.clone();
            let expected_block_parameters = method_key
                .as_ref()
                .and_then(|key| self.declarations.methods.get(key))
                .and_then(|state| state.block.as_ref())
                .and_then(|block| proc_parts(block).map(|(parameters, _)| parameters.to_vec()));
            if let Some(expected) = expected_block_parameters {
                for (index, actual) in argument_types.iter().enumerate() {
                    if let Some(expected) = expected.get(index) {
                        if matches!(expected, Type::Named(name, _) if name.starts_with('{'))
                            && matches!(actual, Type::Hash(_, _))
                        {
                            continue;
                        }
                        if !self.is_assignable(actual, expected) {
                            if let Some(argument) = arguments.argument_nodes.get(index) {
                                let actual_description =
                                    self.argument_type_description(argument, actual);
                                self.error(
                                    argument,
                                    format!(
                                        "Expected `{expected}` but found `{actual_description}` for argument `arg{index}`"
                                    ),
                                );
                            }
                        }
                    }
                }
            }
            if let Some(key) = method_key.as_ref() {
                if let Some(state) = self.declarations.methods.get_mut(key) {
                    if state.observe_yield_arguments(&argument_types) {
                        self.fixpoint.changed_methods.insert(key.clone());
                    }
                }
            }
            let block_return_type = method_key
                .as_ref()
                .and_then(|key| self.declarations.methods.get(key))
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

    fn eval_call_result<'node, C: CallShape<'node>>(
        &mut self,
        node: &Node<'node>,
        call: &C,
        environment: &mut Environment,
    ) -> Eval {
        let mut result = self.eval_call(node, call, environment);
        let type_ =
            self.apply_inline_assertion_in_environment(node, result.type_.clone(), environment);
        if result.normal_type.is_some() {
            result.normal_type = Some(type_.clone());
        }
        result.type_ = self.record(node, type_);
        result
    }

    fn eval_hir_set_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        call: &CallNode<'node>,
        target: &hir::AssignTarget,
        environment: &mut Environment,
    ) -> Eval {
        let receiver_node = call.receiver();
        let receiver_result = if let Some(receiver) = receiver_node.as_ref() {
            self.eval_node(receiver, environment)
        } else {
            Eval::value(environment.self_type.clone())
        };
        let receiver_type = receiver_result.normal_type.clone().unwrap_or(Type::Never);
        let mut argument_nodes = call
            .arguments()
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        let Some(value_node) = argument_nodes.pop() else {
            return Eval::value(self.record(node, Type::Any));
        };

        let (arguments, value_result, setter_name) = match target {
            hir::AssignTarget::Attribute { name, .. } => {
                let value_result = self.eval_node(&value_node, environment);
                let arguments = CallArguments {
                    argument_nodes: vec![value_node],
                    argument_types: value_result
                        .normal_type
                        .as_ref()
                        .into_iter()
                        .cloned()
                        .collect(),
                    positional_indices: vec![0],
                    positional_types: value_result
                        .normal_type
                        .as_ref()
                        .into_iter()
                        .cloned()
                        .collect(),
                    argument_indices: vec![0],
                    ..CallArguments::default()
                };
                (arguments, value_result, format!("{}=", name.as_str()))
            }
            hir::AssignTarget::Index { .. } => {
                let evaluated = self.evaluate_call_arguments(
                    prism_argument_inputs_from_nodes(argument_nodes),
                    environment,
                );
                let mut arguments = evaluated.arguments;
                let value_result = self.eval_node(&value_node, environment);
                if let Some(value_type) = value_result.normal_type.clone() {
                    arguments.argument_nodes.push(value_node);
                    arguments.argument_types.push(value_type.clone());
                    arguments.positional_types.push(value_type);
                    arguments
                        .positional_indices
                        .push(arguments.argument_nodes.len() - 1);
                    arguments
                        .argument_indices
                        .push(arguments.argument_nodes.len() - 1);
                }
                (arguments, value_result, "[]=".to_owned())
            }
            _ => return Eval::value(self.record(node, Type::Any)),
        };

        if let Some(value_type) = value_result.normal_type.as_ref() {
            let site = CallSite {
                argument_nodes: &arguments.argument_nodes,
                argument_types: &arguments.argument_types,
                block: None,
            };
            if let Some(key) = self.receiver_method_key(
                receiver_node.as_ref(),
                &receiver_type,
                &setter_name,
                environment,
            ) {
                let _ = self.eval_resolved_receiver_call(
                    node,
                    &setter_name,
                    &key,
                    &receiver_type,
                    &arguments,
                    None,
                    environment,
                );
            } else {
                let _ = self.eval_method_call(&receiver_type, &setter_name, &site, environment);
            }
            self.refine_local_hash_write(
                receiver_node.as_ref(),
                &setter_name,
                &arguments.argument_types,
                &receiver_type,
                environment,
            );
            let _ = value_type;
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

    fn eval_begin<'node>(
        &mut self,
        node: &Node<'node>,
        begin: &ruby_prism::BeginNode<'node>,
        environment: &mut Environment,
    ) -> Eval {
        let mut entry = environment.clone();
        if let Some(rescue) = begin.rescue_clause() {
            self.bind_rescue_reference_locals(rescue, &mut entry);
        }
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
            if body_flow.contains(FlowKind::Raise) {
                merged_environment = self.join_flow_environments(
                    &merged_environment,
                    body_flow,
                    &rescue_environment,
                    rescue_flow,
                );
            }
        }
        *environment = merged_environment;

        if let Some(ensure) = begin.ensure_clause() {
            if let Some(statements) = ensure.statements() {
                let prior = result;
                // `ensure` runs even when the protected body raises before a
                // local assignment. Include the entry environment so reads
                // in the ensure body retain that possible nil path.
                let mut ensure_environment = environment.join(&entry);
                let ensure_result = self.eval_statements(&statements, &mut ensure_environment);
                *environment = ensure_environment;
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

    fn bind_rescue_reference_locals<'node>(
        &mut self,
        first: ruby_prism::RescueNode<'node>,
        environment: &mut Environment,
    ) {
        let mut next = Some(first);
        while let Some(rescue) = next {
            if let Some(reference) = rescue.reference() {
                self.bind_for_target(&reference, Type::Nil, environment);
            }
            if let Some(statements) = rescue.statements() {
                let mut collector = LocalWriteCollector::default();
                collector.visit(&statements.as_node());
                for name in collector.names {
                    if !environment.contains(&name) {
                        environment.bind(name, Type::Nil);
                    }
                }
            }
            next = rescue.subsequent();
        }
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
            let conditions = when_node.conditions().into_iter().collect::<Vec<_>>();
            let mut when_environment = base.clone();
            let mut condition_type = Type::Never;
            let mut condition_is_type_test = true;
            for value in &conditions {
                let value_type = self.eval_node(&value, &mut when_environment).type_;
                let is_type_test = Self::is_case_type_test(&value, &value_type);
                all_conditions_are_type_tests &= is_type_test;
                condition_is_type_test &= is_type_test;
                let value_type = Self::class_object_value_type(&value_type).unwrap_or(value_type);
                condition_type = condition_type.join(&value_type);
            }
            covered_type = covered_type.join(&condition_type);
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target(predicate, &mut when_environment, &condition_type);
                self.narrow_discriminated_case_target(
                    predicate,
                    &conditions,
                    &mut when_environment,
                );
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
            if let Some(predicate) = predicate.as_ref() {
                self.narrow_case_target_without(
                    predicate,
                    &mut else_environment,
                    &covered_type,
                    all_conditions_are_type_tests,
                );
            }
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
        if let Some(name) = Self::case_target_name(predicate) {
            let current = environment.get(&name);
            environment.bind(name, self.meet_predicate_type(&current, condition_type));
        }
    }

    fn narrow_discriminated_case_target<'node>(
        &self,
        predicate: &Node<'node>,
        conditions: &[Node<'node>],
        environment: &mut Environment,
    ) {
        let Some(call) = predicate.as_call_node() else {
            return;
        };
        if prism::constant_name(call.name()) != "type" {
            return;
        }
        let Some(receiver) = call.receiver() else {
            return;
        };
        let Some(local) = receiver.as_local_variable_read_node() else {
            return;
        };
        let local_name = prism::constant_name(local.name());
        let current = environment.get(&local_name);
        let Some(current_name) = Self::named_type_name(&current) else {
            return;
        };
        let symbols = conditions
            .iter()
            .filter_map(|condition| {
                condition
                    .as_symbol_node()
                    .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
            })
            .collect::<BTreeSet<_>>();
        if symbols.is_empty() {
            return;
        }
        let narrowed = self
            .fixpoint
            .symbol_method_returns
            .iter()
            .filter_map(|(key, symbol)| {
                (key.name == "type"
                    && !key.singleton
                    && symbols.contains(symbol)
                    && key
                        .owner
                        .as_deref()
                        .is_some_and(|owner| self.nominal_subtype(owner, &current_name)))
                .then(|| Type::named(key.owner.as_ref().expect("owner checked").clone()))
            })
            .collect::<Vec<_>>();
        if !narrowed.is_empty() {
            environment.bind(local_name, Type::union(narrowed));
        }
    }

    fn narrow_case_target_without<'node>(
        &self,
        predicate: &Node<'node>,
        environment: &mut Environment,
        excluded: &Type,
        all_conditions_are_type_tests: bool,
    ) {
        if let Some(name) = Self::case_target_name(predicate) {
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
        if let Some(name) = Self::case_target_name(predicate) {
            let current = environment.get(&name);
            environment.bind(name, current.without(excluded));
        }
    }

    fn case_target_name(node: &Node<'_>) -> Option<String> {
        if let Some(parentheses) = node.as_parentheses_node() {
            return parentheses
                .body()
                .and_then(|body| Self::case_target_name(&body));
        }
        if let Some(statements) = node.as_statements_node() {
            return statements
                .body()
                .into_iter()
                .last()
                .and_then(|body| Self::case_target_name(&body));
        }
        node.as_local_variable_read_node()
            .map(|local| prism::constant_name(local.name()))
            .or_else(|| {
                node.as_local_variable_write_node()
                    .map(|write| prism::constant_name(write.name()))
            })
    }

    fn is_case_type_test(node: &Node<'_>, value_type: &Type) -> bool {
        Self::class_object_instance_type(value_type).is_some()
            || node.as_constant_read_node().is_some_and(|constant| {
                matches!(
                    prism::constant_name(constant.name()).as_str(),
                    "Array"
                        | "BasicObject"
                        | "Class"
                        | "Complex"
                        | "FalseClass"
                        | "Float"
                        | "Hash"
                        | "Integer"
                        | "NilClass"
                        | "Numeric"
                        | "Object"
                        | "Rational"
                        | "Regexp"
                        | "String"
                        | "Symbol"
                        | "TrueClass"
                )
            })
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
            if !body_terminal_flow.is_empty() {
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
            let mut collection_result = collection_result;
            collection_result.type_ = self.record(node, collection_result.type_.clone());
            return collection_result;
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
            if !body_terminal_flow.is_empty() {
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
        &mut self,
        target: &Node<'node>,
        type_: Type,
        environment: &mut Environment,
    ) {
        if let Some(target) = target.as_instance_variable_target_node() {
            let name = prism::constant_name(target.name());
            let target_node = target.as_node();
            let type_ =
                self.apply_inline_assertion_in_environment(&target_node, type_, environment);
            // Empty arrays in a tuple-style multi-assignment are open
            // containers. Their element type is bottom only until the first
            // write; retaining `Never` here would make a later append reject
            // every concrete value.
            let type_ = if matches!(&type_, Type::Array(element) if element.is_never()) {
                Type::Array(Box::new(Type::Any))
            } else {
                type_
            };
            self.observe_ivar(environment, name.clone(), &type_, false);
            environment.bind(ivar_refinement_key(&name), type_);
            return;
        }
        if let Some(write) = target.as_local_variable_write_node() {
            let name = prism::constant_name(write.name());
            let open_array = matches!(&type_, Type::Array(element) if element.is_never());
            environment.bind(name.clone(), type_);
            if open_array {
                environment.open_array_locals.insert(name);
            }
            return;
        }
        if let Some(target) = target.as_local_variable_target_node() {
            let name = prism::constant_name(target.name());
            let open_array = matches!(&type_, Type::Array(element) if element.is_never());
            environment.bind(name.clone(), type_);
            if open_array {
                environment.open_array_locals.insert(name);
            }
            return;
        }
        if let Some(required) = target.as_required_parameter_node() {
            environment.bind(prism::constant_name(required.name()), type_);
            return;
        }
        if let Some(multi) = target.as_multi_target_node() {
            let lefts = multi.lefts().into_iter().collect::<Vec<_>>();
            let rights = multi.rights().into_iter().collect::<Vec<_>>();
            let known_length = match &type_ {
                Type::Tuple(elements) => Some(elements.len()),
                _ => None,
            };
            for (index, child) in lefts.iter().enumerate() {
                self.bind_for_target(
                    child,
                    self.multi_assignment_element_type(&type_, index, known_length),
                    environment,
                );
            }
            if let Some(rest) = multi.rest() {
                self.bind_for_target(
                    &rest,
                    Type::Array(Box::new(self.array_element_type(&type_))),
                    environment,
                );
            }
            let right_start = known_length
                .map(|length| lefts.len().max(length.saturating_sub(rights.len())))
                .unwrap_or(lefts.len());
            for (index, child) in rights.iter().enumerate() {
                self.bind_for_target(
                    child,
                    self.multi_assignment_element_type(&type_, right_start + index, known_length),
                    environment,
                );
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
        let report_unreachable = environment.method_key.is_some();
        for child in &body {
            if flow.is_terminated() {
                if report_unreachable {
                    self.error(
                        &child,
                        "This expression appears after an unconditional return",
                    );
                }
                // Sorbet still typechecks dead syntax for diagnostics and
                // reveals. Preserve the enclosing terminated flow while
                // evaluating the child for its own effects.
                let _ = self.eval_node(&child, environment);
                continue;
            }
            let result = self.eval_node(&child, environment);
            abrupt = abrupt.join(&result.abrupt);
            flow = flow.without(FlowKind::Normal).union(result.flow);
            normal_type = result.normal_type;
            if result.flow.is_terminated() {
                normal_type = None;
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
        let registered_key = self
            .declarations
            .definitions
            .get(&prism::span(node).0)
            .cloned()
            .unwrap_or_else(|| MethodKey::top_level(name.clone()));
        let key = if outer
            .method_key
            .as_ref()
            .is_some_and(|method| method.name == "<bound-block>")
        {
            Self::class_object_owner(&outer.self_type).map_or(registered_key.clone(), |owner| {
                MethodKey {
                    owner: Some(owner),
                    name: registered_key.name.clone(),
                    singleton: registered_key.singleton,
                }
            })
        } else {
            registered_key
        };
        if self.filter_method_bodies && !self.fixpoint.active_methods.contains(&key) {
            return Eval::value(Type::Nil);
        }
        self.begin_method_evaluation(&key);
        let previous_substitution_context = self.substitution_context.replace(key.clone());
        let state = self
            .declarations
            .methods
            .get(&key)
            .cloned()
            .unwrap_or_else(|| MethodState::inferred(definition.parameters()));
        if let Some(symbol) = definition
            .body()
            .and_then(|body| Self::trailing_symbol_literal(&body))
        {
            self.fixpoint
                .symbol_method_returns
                .insert(key.clone(), symbol);
        }
        let method_self_type = key.owner.as_ref().map_or(Type::Object, |owner| {
            if key.singleton {
                Self::class_object_type(owner)
            } else if self.is_concern_class_methods_module(owner) {
                // ActiveSupport::Concern copies a `ClassMethods` module into
                // the eventual including class. Its method bodies therefore
                // do not have the module object as `self`; the concrete host
                // is only known at the inclusion site.
                Type::Any
            } else {
                self.instance_self_type(owner)
            }
        });
        let mut method_environment = Environment {
            self_type: method_self_type,
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
            !state.explicit,
        );
        if !state.explicit {
            if let Some(shape) = self.declarations.parameter_shapes.get(&prism::span(node).0) {
                let mut positional_index = 0;
                for (name, kind) in &shape.parameter_kinds {
                    match kind {
                        signature::ParameterKind::Positional
                        | signature::ParameterKind::OptionalPositional
                        | signature::ParameterKind::RestPositional => {
                            if state
                                .params
                                .get(positional_index)
                                .is_some_and(Option::is_some)
                            {
                                method_environment.mark_inferred(name.clone());
                            } else {
                                method_environment.mark_provisional(name.clone());
                            }
                            positional_index += 1;
                        }
                        signature::ParameterKind::Keyword
                        | signature::ParameterKind::OptionalKeyword => {
                            if state.keywords.get(name).is_some_and(Option::is_some) {
                                method_environment.mark_inferred(name.clone());
                            } else {
                                method_environment.mark_provisional(name.clone());
                            }
                        }
                        signature::ParameterKind::RestKeyword | signature::ParameterKind::Block => {
                        }
                    }
                }
            }
        }
        if let Some(parameters) = definition.parameters() {
            if let Some(block) = parameters.block() {
                if let Some(name) = block.name() {
                    let block_type = body_signature.block.clone().unwrap_or_else(|| {
                        Type::Proc(
                            state.block_parameters(),
                            Box::new(state.block_result_type()),
                        )
                    });
                    // Keep the local binding consistent with `bind_parameters`:
                    // an omitted unannotated Ruby block is represented by nil.
                    let block_type = if !state.explicit {
                        Type::union([Type::Nil, block_type])
                    } else {
                        block_type
                    };
                    method_environment.bind(prism::constant_name(name), block_type);
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
        if state.explicit && !state.is_void && !state.is_abstract && !self.is_rbi_definition(node) {
            let expected = self.substitute_method_signature(
                &state.call_signature(),
                Some(&method_environment.self_type),
            );
            let raw_signature = state.call_signature();
            let invalid_attached_class_context =
                (Self::contains_attached_class_type(&raw_signature.return_type)
                    || raw_signature
                        .params
                        .iter()
                        .any(Self::contains_attached_class_type))
                    && !self.attached_class_context_is_valid(&key);
            if !invalid_attached_class_context
                && !inferred_return.is_never()
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
        } else if self.fixpoint.collecting_returns {
            self.record_inferred_return(
                key,
                inferred_return,
                body_result.flow == Flow::abrupt(FlowKind::Raise),
            );
        }
        self.substitution_context = previous_substitution_context;
        let _ = outer;
        Eval::value(self.record(node, Type::Nil))
    }

    fn trailing_symbol_literal<'node>(node: &Node<'node>) -> Option<String> {
        if let Some(statements) = node.as_statements_node() {
            return statements
                .body()
                .into_iter()
                .last()
                .and_then(|last| Self::trailing_symbol_literal(&last));
        }
        node.as_symbol_node()
            .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
    }

    fn is_rbi_definition(&self, node: &Node<'_>) -> bool {
        let (start, end) = prism::span(node);
        self.rbi_ranges
            .iter()
            .any(|(range_start, range_end)| start >= *range_start && end <= *range_end)
    }

    fn is_rbi_offset(&self, offset: usize) -> bool {
        self.rbi_ranges
            .iter()
            .any(|(range_start, range_end)| offset >= *range_start && offset < *range_end)
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
                .declarations
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
            self.evaluate_call_arguments(prism_call_argument_inputs(arguments), environment)
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

    fn bind_parameters<'node>(
        &mut self,
        parameters: Option<ParametersNode<'node>>,
        signature: Option<&MethodSig>,
        environment: &mut Environment,
        block_optional: bool,
    ) {
        let Some(parameters) = parameters else { return };
        let inferred_context = environment
            .method_key
            .as_ref()
            .and_then(|key| self.declarations.methods.get(key))
            .is_some_and(|state| !state.explicit);
        let mut index = 0;
        for parameter in &parameters.requireds() {
            let type_ = signature
                .and_then(|signature| signature.params.get(index))
                .cloned()
                .unwrap_or(Type::Any);
            if parameter.as_multi_target_node().is_some() {
                self.bind_for_target(&parameter, type_, environment);
            } else if let Some(required) = parameter.as_required_parameter_node() {
                self.bind_parameter(environment, required.name(), signature, index);
            }
            index += 1;
        }
        for parameter in &parameters.optionals() {
            if let Some(optional) = parameter.as_optional_parameter_node() {
                self.bind_parameter(environment, optional.name(), signature, index);
                let previous_expected_return = self.expected_return_type.take();
                self.expected_return_type = signature
                    .and_then(|signature| signature.params.get(index))
                    .cloned();
                let mut default_environment = environment.clone();
                self.eval_node(&optional.value(), &mut default_environment);
                self.expected_return_type = previous_expected_return;
                *environment = environment.join(&default_environment);
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
                let previous_expected_return = self.expected_return_type.take();
                self.expected_return_type = signature
                    .and_then(|signature| {
                        signature
                            .keywords
                            .get(&prism::constant_name(optional.name()))
                    })
                    .map(|parameter| parameter.type_.clone());
                self.eval_node(&optional.value(), environment);
                self.expected_return_type = previous_expected_return;
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
                let type_ = signature
                    .and_then(|signature| signature.block.clone())
                    .unwrap_or_else(|| Type::Proc(Vec::new(), Box::new(Type::Any)));
                // A Ruby `&block` local is nil when the caller did not pass a
                // block, even when the method's callable block signature is
                // known. The call-site signature still describes the block
                // accepted by the method; this local needs the runtime
                // nilability so `if block`/`unless block` can refine it.
                let type_ = if block_optional {
                    Type::union([Type::Nil, type_])
                } else {
                    type_
                };
                environment.bind(prism::constant_name(name), type_);
            }
        }
        if inferred_context {
            for parameter in &parameters.requireds() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            for parameter in &parameters.optionals() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            if let Some(rest) = parameters.rest() {
                self.mark_inferred_parameter(&rest, environment);
            }
            for parameter in &parameters.posts() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            for parameter in &parameters.keywords() {
                self.mark_inferred_parameter(&parameter, environment);
            }
            if let Some(rest) = parameters.keyword_rest() {
                self.mark_inferred_parameter(&rest, environment);
            }
            if let Some(block) = parameters.block() {
                if let Some(name) = block.name() {
                    environment.mark_inferred(prism::constant_name(name));
                }
            }
        }
    }

    fn mark_inferred_parameter<'node>(
        &self,
        parameter: &Node<'node>,
        environment: &mut Environment,
    ) {
        if let Some(required) = parameter.as_required_parameter_node() {
            environment.mark_inferred(prism::constant_name(required.name()));
        } else if let Some(optional) = parameter.as_optional_parameter_node() {
            environment.mark_inferred(prism::constant_name(optional.name()));
        } else if let Some(rest) = parameter.as_rest_parameter_node() {
            if let Some(name) = rest.name() {
                environment.mark_inferred(prism::constant_name(name));
            }
        } else if let Some(keyword) = parameter.as_required_keyword_parameter_node() {
            environment.mark_inferred(prism::constant_name(keyword.name()));
        } else if let Some(keyword) = parameter.as_optional_keyword_parameter_node() {
            environment.mark_inferred(prism::constant_name(keyword.name()));
        } else if let Some(rest) = parameter.as_keyword_rest_parameter_node() {
            if let Some(name) = rest.name() {
                environment.mark_inferred(prism::constant_name(name));
            }
        } else if let Some(block) = parameter.as_block_parameter_node() {
            if let Some(name) = block.name() {
                environment.mark_inferred(prism::constant_name(name));
            }
        } else if let Some(multi) = parameter.as_multi_target_node() {
            for target in &multi.lefts() {
                self.mark_inferred_parameter(&target, environment);
            }
            if let Some(rest) = multi.rest() {
                self.mark_inferred_parameter(&rest, environment);
            }
            for target in &multi.rights() {
                self.mark_inferred_parameter(&target, environment);
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
        let parameter_name = prism::constant_name(name);
        environment.bind(parameter_name, type_);
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
        let previous_defer_inline_assertions = self.defer_inline_assertions;
        self.defer_inline_assertions = true;
        let predicate_type = self
            .eval_node(&predicate, environment)
            .normal_type
            .unwrap_or(Type::Never);
        self.defer_inline_assertions = previous_defer_inline_assertions;
        let (then_reachable, else_reachable) =
            self.predicate_reachability(&predicate, environment, &predicate_type);
        let report_unreachable = self.should_report_unreachable_branch(node)
            && self.predicate_is_precise(&predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut then_environment, true);
        let then_result = if let Some(statements) = if_node.statements() {
            if !then_reachable && report_unreachable {
                if let Some(first) = statements.body().into_iter().next() {
                    self.error(&first, "This code is unreachable");
                }
            }
            self.eval_statements(&statements, &mut then_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let then_result = if then_reachable {
            then_result
        } else {
            // Keep checking an unreachable branch for diagnostics, but do not
            // let its return value or control flow affect the enclosing
            // expression's inferred type.
            Eval::unreachable()
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut else_environment, false);
        let else_result = if let Some(subsequent) = if_node.subsequent() {
            if !else_reachable && report_unreachable {
                if let Some(else_clause) = subsequent.as_else_node() {
                    if let Some(statements) = else_clause.statements() {
                        if let Some(first) = statements.body().into_iter().next() {
                            self.error(&first, "This code is unreachable");
                        }
                    }
                }
            }
            self.eval_alternative(&subsequent, &mut else_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let else_result = if else_reachable {
            else_result
        } else {
            Eval::unreachable()
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
        let previous_defer_inline_assertions = self.defer_inline_assertions;
        self.defer_inline_assertions = true;
        let predicate_type = self
            .eval_node(&predicate, environment)
            .normal_type
            .unwrap_or(Type::Never);
        self.defer_inline_assertions = previous_defer_inline_assertions;
        let (predicate_truthy, predicate_falsy) =
            self.predicate_reachability(&predicate, environment, &predicate_type);
        let then_reachable = predicate_falsy;
        let else_reachable = predicate_truthy;
        let report_unreachable = self.should_report_unreachable_branch(node)
            && self.predicate_is_precise(&predicate, environment);

        let mut then_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut then_environment, false);
        let then_result = if let Some(statements) = unless.statements() {
            if !then_reachable && report_unreachable {
                if let Some(first) = statements.body().into_iter().next() {
                    self.error(&first, "This code is unreachable");
                }
            }
            self.eval_statements(&statements, &mut then_environment)
        } else {
            Eval::value(Type::Nil)
        };
        let then_result = if then_reachable {
            then_result
        } else {
            Eval::value(Type::Never)
        };

        let mut else_environment = environment.clone();
        self.narrow_from_predicate(&predicate, &mut else_environment, true);
        let else_result = if let Some(else_clause) = unless.else_clause() {
            if let Some(statements) = else_clause.statements() {
                if !else_reachable && report_unreachable {
                    if let Some(first) = statements.body().into_iter().next() {
                        self.error(&first, "This code is unreachable");
                    }
                }
                self.eval_statements(&statements, &mut else_environment)
            } else {
                Eval::value(Type::Nil)
            }
        } else {
            Eval::value(Type::Nil)
        };
        let else_result = if else_reachable {
            else_result
        } else {
            Eval::value(Type::Never)
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

    fn predicate_reachability<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
        predicate_type: &Type,
    ) -> (bool, bool) {
        if let Some(parentheses) = node.as_parentheses_node() {
            if let Some(body) = parentheses.body() {
                return self.predicate_reachability(&body, environment, predicate_type);
            }
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            if environment.is_inferred(&name) {
                return (true, true);
            }
            if let Some(truthy) = environment.known_truthiness(&name) {
                return (truthy, !truthy);
            }
            if let Some(alias) = environment.predicate_alias(&name) {
                let source_type = environment.get(&alias.source);
                let (then_reachable, else_reachable) = if let Some(expected) = &alias.expected {
                    (
                        !source_type.meet(expected).is_never(),
                        !source_type.without(expected).is_never(),
                    )
                } else {
                    (
                        !source_type.truthy_part().is_never(),
                        !source_type.falsy_part().is_never(),
                    )
                };
                return if alias.negated {
                    (else_reachable, then_reachable)
                } else {
                    (then_reachable, else_reachable)
                };
            }
            let type_ = environment.get(&name);
            return (
                !type_.truthy_part().is_never(),
                !type_.falsy_part().is_never(),
            );
        }
        if let Some(and) = node.as_and_node() {
            let left = self.predicate_reachability(
                &and.left(),
                environment,
                &self.predicate_type_for_node(&and.left(), environment, predicate_type),
            );
            let right = self.predicate_reachability(
                &and.right(),
                environment,
                &self.predicate_type_for_node(&and.right(), environment, predicate_type),
            );
            return (left.0 && right.0, left.1 || (left.0 && right.1));
        }
        if let Some(or) = node.as_or_node() {
            let left = self.predicate_reachability(
                &or.left(),
                environment,
                &self.predicate_type_for_node(&or.left(), environment, predicate_type),
            );
            let right = self.predicate_reachability(
                &or.right(),
                environment,
                &self.predicate_type_for_node(&or.right(), environment, predicate_type),
            );
            return (left.0 || (left.1 && right.0), left.1 && right.1);
        }
        if let Some(call) = node.as_call_node() {
            let name = prism::constant_name(call.name());
            if call.receiver().is_some_and(|receiver| {
                receiver.as_local_variable_read_node().is_some_and(|local| {
                    environment.is_inferred(&prism::constant_name(local.name()))
                })
            }) {
                return (true, true);
            }
            if name == "==="
                && call.arguments().is_some_and(|arguments| {
                    arguments.arguments().into_iter().any(|argument| {
                        argument.as_local_variable_read_node().is_some_and(|local| {
                            environment.is_inferred(&prism::constant_name(local.name()))
                        })
                    })
                })
            {
                return (true, true);
            }
            if name == "!" {
                if let Some(receiver) = call.receiver() {
                    let can_refine_receiver = receiver.as_local_variable_read_node().is_some()
                        || receiver.as_parentheses_node().is_some()
                        || receiver
                            .as_call_node()
                            .is_some_and(|call| prism::constant_name(call.name()) == "!");
                    if can_refine_receiver {
                        let (then_reachable, else_reachable) =
                            self.predicate_reachability(&receiver, environment, predicate_type);
                        return (else_reachable, then_reachable);
                    }
                    if let Some(receiver_type) = self.recorded_node_type(&receiver) {
                        return (
                            !receiver_type.falsy_part().is_never(),
                            !receiver_type.truthy_part().is_never(),
                        );
                    }
                }
            } else if name == "block_given?" && call.receiver().is_none() {
                let required = environment
                    .method_key
                    .as_ref()
                    .and_then(|key| self.declarations.methods.get(key))
                    .is_some_and(|state| state.explicit && state.block.is_some());
                if required {
                    return (true, false);
                }
            } else if name == "nil?" {
                if let Some(receiver) = call.receiver() {
                    if let Some(receiver_type) = self.recorded_node_type(&receiver) {
                        return (
                            !receiver_type.meet(&Type::Nil).is_never(),
                            !receiver_type.without(&Type::Nil).is_never(),
                        );
                    }
                }
            } else if matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?") {
                if let (Some(receiver), Some(arguments)) = (
                    call.receiver(),
                    call.arguments()
                        .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>()),
                ) {
                    if let Some(local) = receiver.as_local_variable_read_node() {
                        if let Some(argument) = arguments.first() {
                            let current = environment.get(&prism::constant_name(local.name()));
                            let expected = self.predicate_expected_type(argument, environment);
                            let truthy = self.meet_predicate_type(&current, &expected);
                            let falsy = current.without(&expected);
                            return (!truthy.is_never(), !falsy.is_never());
                        }
                    }
                }
            }
        }
        (
            !predicate_type.truthy_part().is_never(),
            !predicate_type.falsy_part().is_never(),
        )
    }

    fn predicate_type_for_node<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
        fallback: &Type,
    ) -> Type {
        self.recorded_node_type(node).unwrap_or_else(|| {
            node.as_local_variable_read_node()
                .map(|local| environment.get(&prism::constant_name(local.name())))
                .unwrap_or_else(|| fallback.clone())
        })
    }

    fn predicate_is_precise<'node>(&self, node: &Node<'node>, environment: &Environment) -> bool {
        if let Some(parentheses) = node.as_parentheses_node() {
            return parentheses
                .body()
                .is_some_and(|body| self.predicate_is_precise(&body, environment));
        }
        if node.as_statements_node().is_some_and(|statements| {
            statements
                .body()
                .into_iter()
                .last()
                .is_some_and(|last| self.predicate_is_precise(&last, environment))
        }) {
            return true;
        }
        if node.as_true_node().is_some()
            || node.as_false_node().is_some()
            || node.as_nil_node().is_some()
            || node.as_integer_node().is_some()
            || node.as_string_node().is_some()
        {
            return true;
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            return !environment.is_inferred(&name)
                && (environment.known_truthiness(&name).is_some()
                    || !environment.get(&name).is_any());
        }
        if let Some(and) = node.as_and_node() {
            return self.predicate_is_precise(&and.left(), environment)
                && self.predicate_is_precise(&and.right(), environment);
        }
        if let Some(or) = node.as_or_node() {
            return self.predicate_is_precise(&or.left(), environment)
                && self.predicate_is_precise(&or.right(), environment);
        }
        let Some(call) = node.as_call_node() else {
            return false;
        };
        let name = prism::constant_name(call.name());
        if call.receiver().is_some_and(|receiver| {
            receiver
                .as_local_variable_read_node()
                .is_some_and(|local| environment.is_inferred(&prism::constant_name(local.name())))
        }) {
            return false;
        }
        if name == "==="
            && call.arguments().is_some_and(|arguments| {
                arguments.arguments().into_iter().any(|argument| {
                    argument.as_local_variable_read_node().is_some_and(|local| {
                        environment.is_inferred(&prism::constant_name(local.name()))
                    })
                })
            })
        {
            return false;
        }
        if name == "!" {
            return call
                .receiver()
                .is_some_and(|receiver| self.predicate_is_precise(&receiver, environment));
        }
        if name == "block_given?" && call.receiver().is_none() {
            // Sorbet uses a required callable block in the surrounding
            // signature to typecheck the false arm as unreachable, but does
            // not emit an unreachable-code diagnostic for this Ruby idiom.
            return false;
        }
        if matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?")
            && call.receiver().is_some()
            && call
                .arguments()
                .is_some_and(|arguments| !arguments.arguments().is_empty())
        {
            return call.receiver().is_some_and(|receiver| {
                receiver.as_local_variable_read_node().is_some_and(|local| {
                    !environment
                        .get(&prism::constant_name(local.name()))
                        .is_any()
                })
            });
        }
        if let Some(receiver) = call.receiver() {
            let receiver_type = self.recorded_node_type(&receiver).or_else(|| {
                receiver
                    .as_local_variable_read_node()
                    .map(|local| environment.get(&prism::constant_name(local.name())))
            });
            if let Some(receiver_type) = receiver_type {
                if let Some(key) =
                    self.receiver_method_key(Some(&receiver), &receiver_type, &name, environment)
                {
                    return self
                        .resolve_method_key(&key)
                        .and_then(|resolved| self.declarations.methods.get(&resolved))
                        .is_some_and(|state| state.explicit);
                }
            }
        } else {
            let key = self.implicit_method_key(&name, environment);
            return self
                .resolve_method_key(&key)
                .and_then(|resolved| self.declarations.methods.get(&resolved))
                .is_some_and(|state| state.explicit);
        }
        false
    }

    fn recorded_node_type(&self, node: &Node<'_>) -> Option<Type> {
        let (start, end) = prism::span(node);
        self.types
            .iter()
            .rev()
            .find(|inferred| inferred.start == start && inferred.end == end)
            .map(|inferred| inferred.type_.clone())
    }

    fn should_report_unreachable_branch(&self, node: &Node<'_>) -> bool {
        let start = prism::span(node).0;
        self.source[..start]
            .iter()
            .rev()
            .find(|byte| !byte.is_ascii_whitespace())
            .is_none_or(|byte| *byte != b'=')
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
            if truthy {
                let left = self.positive_type_test(&or.left(), environment);
                let right = self.positive_type_test(&or.right(), environment);
                if let (Some((left_name, left_type)), Some((right_name, right_type))) =
                    (left, right)
                {
                    if left_name == right_name {
                        let expected = left_type.join(&right_type);
                        if left_name == "<self>" {
                            let current = environment.self_type.clone();
                            environment.self_type = self.meet_predicate_type(&current, &expected);
                        } else {
                            let current = environment.get(&left_name);
                            environment
                                .bind(left_name, self.meet_predicate_type(&current, &expected));
                        }
                    }
                }
            } else {
                let left = or.left();
                self.narrow_from_predicate(&left, environment, false);
                let right = or.right();
                self.narrow_from_predicate(&right, environment, false);
            }
            return;
        }
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            if environment.is_inferred(&name) {
                return;
            }
            if let Some(alias) = environment.predicate_alias(&name).cloned() {
                let source_current = environment.get(&alias.source);
                let source_truthy = if alias.negated { !truthy } else { truthy };
                let source_narrowed = if let Some(expected) = alias.expected.as_ref() {
                    if source_truthy {
                        source_current.meet(&expected)
                    } else {
                        source_current.without(&expected)
                    }
                } else if source_truthy {
                    source_current.truthy_part()
                } else {
                    source_current.falsy_part()
                };
                environment.bind(alias.source.clone(), source_current.meet(&source_narrowed));
                if alias.expected.is_none() {
                    environment.set_known_truthiness(alias.source, source_truthy);
                }
            }
            let current = environment.get(&name);
            let narrowed = if truthy {
                current.truthy_part()
            } else {
                current.falsy_part()
            };
            environment.bind(name.clone(), current.meet(&narrowed));
            environment.set_known_truthiness(name, truthy);
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
            environment.bind(name.clone(), current.meet(&narrowed));
            environment.set_known_truthiness(name, truthy);
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
            if truthy
                && name == "string?"
                && call.receiver().as_ref().is_some_and(|receiver| {
                    self.constant_reference_name(receiver)
                        .is_some_and(|name| self.nominal_names_match(&name, "NodeHelpers"))
                })
            {
                if let Some(argument) = arguments.first() {
                    if let Some(local) = argument.as_local_variable_read_node() {
                        let name = prism::constant_name(local.name());
                        let current = environment.get(&name);
                        environment.bind(
                            name,
                            Type::intersection([current, Type::named("AST::StringNode")]),
                        );
                    }
                }
            }
            if let Some(receiver) = receiver {
                if name == "===" && arguments.len() == 1 {
                    if let Some(local) = arguments[0].as_local_variable_read_node() {
                        let local_name = prism::constant_name(local.name());
                        let class_type = self.node_type(&receiver, environment);
                        let expected = Self::class_object_value_type(&class_type)
                            .unwrap_or_else(|| class_type.clone());
                        let current = environment.get(&local_name);
                        let narrowed = if truthy {
                            self.meet_predicate_type(&current, &expected)
                        } else {
                            current.without(&expected)
                        };
                        environment.bind(local_name, narrowed);
                        return;
                    }
                    if let Some(instance_variable) = arguments[0].as_instance_variable_read_node() {
                        let class_type = self.node_type(&receiver, environment);
                        let expected = Self::class_object_value_type(&class_type)
                            .unwrap_or_else(|| class_type.clone());
                        let instance_variable_name = prism::constant_name(instance_variable.name());
                        let current = self.ivar_type(environment, &instance_variable_name);
                        let narrowed = if truthy {
                            self.meet_predicate_type(&current, &expected)
                        } else {
                            current.without(&expected)
                        };
                        environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                        return;
                    }
                }
                if truthy && name == "==" && arguments.len() == 1 {
                    if let Some(arity_call) = receiver.as_call_node() {
                        if prism::constant_name(arity_call.name()) == "arity"
                            && arity_call.arguments().is_none()
                        {
                            if let Some(block_local) = arity_call
                                .receiver()
                                .and_then(|receiver| receiver.as_local_variable_read_node())
                            {
                                if let Some(integer) = arguments[0].as_integer_node() {
                                    let value: Result<i32, _> = integer.value().try_into();
                                    if let Ok(value) = value {
                                        if let Ok(arity) = usize::try_from(value) {
                                            let block_name =
                                                prism::constant_name(block_local.name());
                                            if !environment.is_inferred(&block_name) {
                                                let current = environment.get(&block_name);
                                                if let Some(narrowed) =
                                                    proc_arity_narrowing(&current, arity)
                                                {
                                                    environment.bind(block_name, narrowed);
                                                    return;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if name == "empty?" {
                    if let Some(local) = receiver.as_local_variable_read_node() {
                        let local_name = prism::constant_name(local.name());
                        if matches!(
                            environment.get(&local_name),
                            Type::Array(_) | Type::Tuple(_)
                        ) {
                            environment.set_known_nonempty_array(&local_name, !truthy);
                        }
                        return;
                    }
                }
                if let Some(local) = receiver.as_local_variable_read_node() {
                    let local_name = prism::constant_name(local.name());
                    if environment.is_inferred(&local_name) {
                        return;
                    }
                    let current = environment.get(&local_name);
                    if matches!(name.as_str(), "<" | "<=") && arguments.len() == 1 {
                        let expected = self.resolve_type_names(
                            &self.predicate_expected_type(&arguments[0], environment),
                            None,
                        );
                        let narrowed =
                            self.class_object_subclass_narrowing(&current, &expected, truthy);
                        environment.bind(local_name, narrowed);
                        return;
                    }
                    if let Some(narrowed) = self.equality_predicate_narrowing(
                        &name,
                        &current,
                        &arguments,
                        truthy,
                        environment,
                    ) {
                        environment.bind(local_name, narrowed);
                        return;
                    }
                    let safe_navigation_non_nil = call.is_safe_navigation()
                        && (truthy
                            || self.safe_navigation_method_returns_non_nil(
                                &receiver,
                                &current,
                                &name,
                                &arguments,
                                environment,
                            ));
                    let narrowed = match name.as_str() {
                        "nil?" => {
                            if truthy {
                                current.meet(&Type::Nil)
                            } else {
                                current.without(&Type::Nil)
                            }
                        }
                        "is_a?" | "kind_of?" | "instance_of?" if !arguments.is_empty() => {
                            let expected = self.predicate_expected_type(&arguments[0], environment);
                            if truthy {
                                self.meet_predicate_type(&current, &expected)
                            } else {
                                current.without(&expected)
                            }
                        }
                        _ if safe_navigation_non_nil => current.without(&Type::Nil),
                        _ => return,
                    };
                    environment.bind(local_name, narrowed);
                } else if let Some(instance_variable) = receiver.as_instance_variable_read_node() {
                    let instance_variable_name = prism::constant_name(instance_variable.name());
                    let current = self.ivar_type(environment, &instance_variable_name);
                    if truthy && name == "===" && arguments.len() == 1 {
                        let class_type = self.node_type(&receiver, environment);
                        let expected = Self::class_object_value_type(&class_type)
                            .unwrap_or_else(|| class_type.clone());
                        environment.bind(
                            ivar_refinement_key(&instance_variable_name),
                            self.meet_predicate_type(&current, &expected),
                        );
                        return;
                    }
                    if let Some(narrowed) = self.equality_predicate_narrowing(
                        &name,
                        &current,
                        &arguments,
                        truthy,
                        environment,
                    ) {
                        environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                        return;
                    }
                    let safe_navigation_non_nil = call.is_safe_navigation()
                        && (truthy
                            || self.safe_navigation_method_returns_non_nil(
                                &receiver,
                                &current,
                                &name,
                                &arguments,
                                environment,
                            ));
                    let narrowed = match name.as_str() {
                        "nil?" => {
                            if truthy {
                                current.meet(&Type::Nil)
                            } else {
                                current.without(&Type::Nil)
                            }
                        }
                        "is_a?" | "kind_of?" | "instance_of?" if !arguments.is_empty() => {
                            let expected = self.predicate_expected_type(&arguments[0], environment);
                            if truthy {
                                self.meet_predicate_type(&current, &expected)
                            } else {
                                current.without(&expected)
                            }
                        }
                        _ if safe_navigation_non_nil => current.without(&Type::Nil),
                        _ => return,
                    };
                    environment.bind(ivar_refinement_key(&instance_variable_name), narrowed);
                }
            } else if matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?")
                && !arguments.is_empty()
            {
                let current = environment.self_type.clone();
                let expected = self.predicate_expected_type(&arguments[0], environment);
                environment.self_type = if truthy {
                    self.meet_predicate_type(&current, &expected)
                } else {
                    current.without(&expected)
                };
            }
        }
    }

    fn positive_type_test<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Option<(String, Type)> {
        let call = node.as_call_node()?;
        let name = prism::constant_name(call.name());
        if !matches!(name.as_str(), "is_a?" | "kind_of?" | "instance_of?") {
            return None;
        }
        let argument = call
            .arguments()
            .and_then(|arguments| arguments.arguments().into_iter().next())?;
        let local = match call.receiver() {
            None => "<self>".to_owned(),
            Some(receiver) => {
                let local = receiver.as_local_variable_read_node()?;
                let name = prism::constant_name(local.name());
                if environment.is_inferred(&name) {
                    return None;
                }
                name
            }
        };
        Some((local, self.predicate_expected_type(&argument, environment)))
    }

    fn meet_predicate_type(&self, current: &Type, expected: &Type) -> Type {
        if let Type::Union(members) = current {
            return Type::union(
                members
                    .iter()
                    .map(|member| self.meet_predicate_type(member, expected)),
            );
        }
        if self.is_assignable(expected, current) {
            expected.clone()
        } else if self.is_assignable(current, expected) {
            // The current type may be a more precise structural form of the
            // predicate's nominal class. For example, a fixed tuple is an
            // Array, but intersecting it with the bare `Array` nominal would
            // discard its element positions and route `[]` through the
            // unparameterized fallback model.
            current.clone()
        } else if Self::definitely_disjoint_class_types(self, current, expected) {
            Type::Never
        } else {
            current.meet(expected)
        }
    }

    fn class_object_subclass_narrowing(
        &self,
        current: &Type,
        expected: &Type,
        truthy: bool,
    ) -> Type {
        if !truthy {
            return current.clone();
        }
        match current {
            Type::Union(members) => Type::union(members.iter().filter_map(|member| {
                let narrowed = self.class_object_subclass_narrowing(member, expected, true);
                (!narrowed.is_never()).then_some(narrowed)
            })),
            Type::Intersection(members) => {
                let mut narrowed = Vec::new();
                for member in members {
                    let next = if Self::is_class_or_module_object(member) {
                        self.class_object_subclass_narrowing(member, expected, true)
                    } else {
                        member.clone()
                    };
                    if next.is_never() {
                        return Type::Never;
                    }
                    narrowed.push(next);
                }
                Type::intersection(narrowed)
            }
            Type::Named(name, arguments)
                if name_matches(name, "Class") || name_matches(name, "Module") =>
            {
                if arguments.is_empty() {
                    return Type::Named(name.clone(), vec![expected.clone()]);
                }
                let instance = arguments.first().cloned().unwrap_or(Type::Any);
                if let Type::Union(members) = &instance {
                    let narrowed = Type::union(members.iter().filter_map(|member| {
                        if self.is_assignable(member, expected) {
                            Some(member.clone())
                        } else if Self::definitely_disjoint_class_types(self, member, expected) {
                            None
                        } else {
                            let member = member.meet(expected);
                            (!member.is_never()).then_some(member)
                        }
                    }));
                    return if narrowed.is_never() {
                        Type::Never
                    } else {
                        Type::Named(name.clone(), vec![narrowed])
                    };
                }
                if !instance.is_any() && self.is_assignable(&instance, expected) {
                    return current.clone();
                }
                if Self::definitely_disjoint_class_types(self, &instance, expected) {
                    return Type::Never;
                }
                let instance = instance.meet(expected);
                if instance.is_never() {
                    Type::Never
                } else {
                    Type::Named(name.clone(), vec![instance])
                }
            }
            _ => current.clone(),
        }
    }

    fn is_class_or_module_object(type_: &Type) -> bool {
        matches!(
            type_,
            Type::Named(name, _) if name_matches(name, "Class") || name_matches(name, "Module")
        )
    }

    fn definitely_disjoint_class_types(&self, actual: &Type, expected: &Type) -> bool {
        let Some(actual_name) = Self::class_instance_name(actual) else {
            return false;
        };
        let Some(expected_name) = Self::class_instance_name(expected) else {
            return false;
        };
        if !self.known_nominal_name(&actual_name) || !self.known_nominal_name(&expected_name) {
            return false;
        }
        // A Ruby class can include a module (and a module can be mixed into
        // another module), so two nominal names are not enough to prove that
        // this refinement is impossible. Sorbet keeps the class-object
        // intersection in cases such as `klass < Exportable`.
        if self
            .declarations
            .classes
            .get(&actual_name)
            .is_some_and(|info| info.is_module)
            || self
                .declarations
                .classes
                .get(&expected_name)
                .is_some_and(|info| info.is_module)
        {
            return false;
        }
        !self.nominal_subtype(&actual_name, &expected_name)
            && !self.nominal_subtype(&expected_name, &actual_name)
    }

    fn class_instance_name(type_: &Type) -> Option<String> {
        match type_ {
            Type::Named(name, _) => Some(name.clone()),
            Type::Integer => Some("Integer".to_owned()),
            Type::Float => Some("Float".to_owned()),
            Type::String => Some("String".to_owned()),
            Type::Symbol => Some("Symbol".to_owned()),
            Type::Object => Some("Object".to_owned()),
            _ => None,
        }
    }

    fn known_nominal_name(&self, name: &str) -> bool {
        self.declarations.classes.contains_key(name)
            || matches!(name, "ActiveSupport::Inflector")
            || matches!(
                name.rsplit_once("::").map_or(name, |(_, tail)| tail),
                "BasicObject"
                    | "Object"
                    | "Kernel"
                    | "Numeric"
                    | "Integer"
                    | "Float"
                    | "Rational"
                    | "Complex"
                    | "String"
                    | "Symbol"
                    | "Array"
                    | "Hash"
                    | "Range"
                    | "Regexp"
                    | "MatchData"
                    | "Encoding"
                    | "Time"
                    | "Date"
                    | "DateTime"
                    | "Class"
                    | "Module"
                    | "Proc"
                    | "Binding"
                    | "Method"
                    | "UnboundMethod"
                    | "Enumerator"
                    | "Struct"
                    | "Thread"
                    | "Mutex"
                    | "Ractor"
                    | "Fiber"
                    | "IO"
                    | "File"
                    | "Dir"
                    | "ENV"
                    | "ARGF"
                    | "Set"
                    | "Random"
                    | "SecureRandom"
                    | "OptionParser"
                    | "JSON"
                    | "Psych"
                    | "YAML"
                    | "ActiveSupport"
                    | "ActiveSupport::Inflector"
                    | "Exception"
                    | "StandardError"
                    | "RuntimeError"
                    | "ArgumentError"
                    | "TypeError"
                    | "NameError"
                    | "NoMethodError"
                    | "IOError"
                    | "SystemCallError"
                    | "NilClass"
                    | "TrueClass"
                    | "FalseClass"
            )
    }

    fn predicate_alias_for_value<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Option<PredicateAlias> {
        if let Some(local) = node.as_local_variable_read_node() {
            let name = prism::constant_name(local.name());
            return environment
                .predicate_alias(&name)
                .cloned()
                .or(Some(PredicateAlias {
                    source: name,
                    negated: false,
                    expected: None,
                }));
        }
        let call = node.as_call_node()?;
        let name = prism::constant_name(call.name());
        if name == "!" {
            let receiver = call.receiver()?;
            if let Some(inner_call) = receiver.as_call_node() {
                let mut alias = self.predicate_alias_from_call(&inner_call, environment)?;
                alias.negated = !alias.negated;
                return Some(alias);
            }
            let local = receiver.as_local_variable_read_node()?;
            let name = prism::constant_name(local.name());
            if let Some(alias) = environment.predicate_alias(&name) {
                Some(PredicateAlias {
                    source: alias.source.clone(),
                    negated: !alias.negated,
                    expected: alias.expected.clone(),
                })
            } else {
                Some(PredicateAlias {
                    source: name,
                    negated: true,
                    expected: None,
                })
            }
        } else {
            self.predicate_alias_from_call(&call, environment)
        }
    }

    fn predicate_alias_from_call<'node>(
        &self,
        call: &CallNode<'node>,
        environment: &Environment,
    ) -> Option<PredicateAlias> {
        let name = prism::constant_name(call.name());
        if !matches!(
            name.as_str(),
            "nil?" | "is_a?" | "kind_of?" | "instance_of?"
        ) {
            return None;
        }
        let receiver = call.receiver()?;
        let local = receiver.as_local_variable_read_node()?;
        let source = prism::constant_name(local.name());
        let expected = if name == "nil?" {
            Type::Nil
        } else {
            let arguments = call
                .arguments()
                .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
                .unwrap_or_default();
            if arguments.is_empty() {
                return None;
            }
            self.predicate_expected_type(&arguments[0], environment)
        };
        Some(PredicateAlias {
            source,
            negated: false,
            expected: Some(expected),
        })
    }

    fn equality_predicate_narrowing<'node>(
        &mut self,
        name: &str,
        current: &Type,
        arguments: &[Node<'node>],
        truthy: bool,
        environment: &Environment,
    ) -> Option<Type> {
        if !matches!(name, "==" | "!=" | "equal?" | "eql?") || arguments.len() != 1 {
            return None;
        }
        let argument_type = self.node_type(&arguments[0], environment);
        let singleton = matches!(argument_type, Type::Nil | Type::True | Type::False);
        Some(match (name, truthy) {
            ("==" | "equal?" | "eql?", true) | ("!=", false) => current.meet(&argument_type),
            ("==" | "equal?" | "eql?", false) | ("!=", true) if singleton => {
                current.without(&argument_type)
            }
            ("==" | "equal?" | "eql?", false) | ("!=", true) => current.clone(),
            _ => current.clone(),
        })
    }

    fn predicate_expected_type<'node>(
        &self,
        node: &Node<'node>,
        environment: &Environment,
    ) -> Type {
        if let Some(call) = node.as_call_node() {
            if prism::constant_name(call.name()) == "unsafe"
                && call.receiver().as_ref().is_some_and(|receiver| {
                    self.constant_reference_name(receiver)
                        .is_some_and(|name| name.trim_start_matches("::") == "T")
                })
            {
                // `T.unsafe(x)` deliberately erases the expression's type.
                // In particular, `klass <= T.unsafe(Integer)` must not
                // refine a class object to `Class[Integer]`.
                return Type::Any;
            }
            if prism::constant_name(call.name()) == "class"
                && call
                    .receiver()
                    .as_ref()
                    .is_some_and(|receiver| receiver.as_self_node().is_some())
            {
                return environment.self_type.clone();
            }
        }
        let type_ = signature::parse_type(&prism::text(self.source, node));
        let owner = self.lexical_owner(environment);
        match self.resolve_type_names(&type_, owner.as_deref()) {
            Type::Named(name, arguments)
                if arguments.is_empty()
                    && (name_matches(&name, "Class") || name_matches(&name, "Module")) =>
            {
                Type::Named(name, vec![Type::Anything])
            }
            type_ => type_,
        }
    }

    fn safe_navigation_method_returns_non_nil<'node>(
        &mut self,
        receiver: &Node<'node>,
        receiver_type: &Type,
        name: &str,
        arguments: &[Node<'node>],
        environment: &mut Environment,
    ) -> bool {
        let receiver_type = receiver_type.without(&Type::Nil);
        if receiver_type.is_any() {
            return false;
        }
        if let Some(key) =
            self.receiver_method_key(Some(receiver), &receiver_type, name, environment)
        {
            if let Some(resolved) = self.resolve_method_key(&key) {
                if let Some(state) = self.declarations.methods.get(&resolved) {
                    let return_type = state.call_signature().return_type;
                    return !return_type.is_any() && return_type.without(&Type::Nil) == return_type;
                }
            }
        }
        let site = CallSite {
            argument_nodes: arguments,
            argument_types: &[],
            block: None,
        };
        let return_type = self.eval_method_call(&receiver_type, name, &site, environment);
        !return_type.is_any() && return_type.without(&Type::Nil) == return_type
    }

    fn refine_local_array_write(
        &self,
        receiver_node: Option<&Node<'_>>,
        name: &str,
        argument_types: &[Type],
        receiver_type: &Type,
        environment: &mut Environment,
    ) {
        if !matches!(name, "push" | "<<" | "prepend") {
            return;
        }
        let Some(local) = receiver_node.and_then(Node::as_local_variable_read_node) else {
            return;
        };
        let Type::Array(element) = receiver_type else {
            return;
        };
        let open_array = environment
            .open_array_locals
            .contains(&prism::constant_name(local.name()));
        let mut refined_element = element.as_ref().clone();
        for actual in argument_types {
            if !open_array && !self.is_assignable(actual, element) {
                continue;
            }
            if refined_element.is_any() && !actual.is_any() {
                refined_element = actual.clone();
            } else {
                refined_element = refined_element.join(actual);
            }
        }
        if refined_element != element.as_ref().clone() {
            environment.bind(
                prism::constant_name(local.name()),
                Type::Array(Box::new(refined_element)),
            );
            if open_array {
                environment
                    .open_array_locals
                    .insert(prism::constant_name(local.name()));
            }
        }
    }

    fn refine_local_hash_write(
        &self,
        receiver_node: Option<&Node<'_>>,
        name: &str,
        argument_types: &[Type],
        receiver_type: &Type,
        environment: &mut Environment,
    ) {
        if name != "[]=" {
            return;
        }
        let Some(local) = receiver_node.and_then(Node::as_local_variable_read_node) else {
            return;
        };
        let Type::Hash(key, value) = receiver_type else {
            return;
        };
        let Some(actual_key) = argument_types.first() else {
            return;
        };
        let Some(actual_value) = argument_types.last() else {
            return;
        };
        let refined_key = if key.is_any() && !actual_key.is_any() {
            actual_key.clone()
        } else {
            key.join(actual_key)
        };
        let refined_value = if value.is_any() && !actual_value.is_any() {
            actual_value.clone()
        } else {
            value.join(actual_value)
        };
        if refined_key != key.as_ref().clone() || refined_value != value.as_ref().clone() {
            environment.bind(
                prism::constant_name(local.name()),
                Type::Hash(Box::new(refined_key), Box::new(refined_value)),
            );
        }
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
            if matches!(name, "call" | "[]")
                && members.iter().all(|member| {
                    member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
                })
            {
                let type_ = self.eval_method_call(receiver_type, name, site, environment);
                return (type_, UntypedOrigin::InferredMethod);
            }
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

        // `T.class_of(Foo)[T.all(Foo, M)]` is still a class object whose
        // singleton methods come from Foo. Look up those methods through the
        // intersected instance members while retaining the full receiver for
        // `T.attached_class` substitution.
        if let Type::Named(class, type_arguments) = receiver_type {
            if (name_matches(class, "Class") || name_matches(class, "Module"))
                && type_arguments
                    .first()
                    .is_some_and(|argument| matches!(argument, Type::Intersection(_)))
            {
                if let Some(Type::Intersection(members)) = type_arguments.first() {
                    for member in members {
                        let candidate = Type::Named(class.clone(), vec![member.clone()]);
                        let Some(key) =
                            self.receiver_method_key(receiver_node, &candidate, name, environment)
                        else {
                            continue;
                        };
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
                }
            }
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
        let resolved_owner = self
            .resolve_method_key(key)
            .and_then(|resolved| resolved.owner);
        if self
            .resolve_method_key(key)
            .and_then(|resolved| self.declarations.methods.get(&resolved))
            .is_some_and(|state| state.visibility == Visibility::Private)
            && !self.private_call_allowed(key, environment)
        {
            self.error(
                node,
                format!("Non-private call to private method `{name}` on `{receiver_type}`"),
            );
            return Some((Type::Any, true));
        }
        if let Some(type_) =
            self.eval_tsort_method(receiver_type, name, environment, resolved_owner.as_deref())
        {
            return Some((type_, false));
        }
        if matches!(receiver_type, Type::Tuple(_))
            && matches!(name, "first" | "last")
            && arguments.argument_types.is_empty()
        {
            // A fixed tuple is more precise than the generic Array RBI.  In
            // particular, `const_source_location(...).first` is known to be
            // the tuple's String component, not an unresolved Array::Elem.
            return Some((
                self.eval_method_call(
                    receiver_type,
                    name,
                    &CallSite {
                        argument_nodes: &arguments.argument_nodes,
                        argument_types: &arguments.argument_types,
                        block,
                    },
                    environment,
                ),
                false,
            ));
        }
        self.record_method_dependency(key, environment);
        let inferred_accessor = self
            .resolve_method_key(key)
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
        let signature = self.widen_overridable_noreturn(key, signature);
        let declared = self
            .resolve_method_key(key)
            .and_then(|resolved| self.declarations.methods.get(&resolved))
            .is_some_and(|state| state.explicit);
        let block_return_type = self.observe_block_call(
            key,
            block,
            &signature,
            arguments,
            Some(receiver_type),
            environment,
        );
        let type_ = if let Some(type_) =
            self.eval_node_helpers_method(receiver_type, name, &arguments.argument_types)
        {
            type_
        } else {
            self.invoke_signature(
                node,
                name,
                &signature,
                arguments,
                Some(receiver_type),
                block_return_type.as_ref(),
            )
        };
        let type_ = self.widen_recursive_call_return(key, type_, environment);
        Some((type_, declared))
    }

    /// An inferred method whose only observed path raises is provisionally
    /// represented as `T.noreturn`. That is useful for local helper methods,
    /// but it is not sound for an ordinary Ruby instance method: subclasses
    /// can override it and return normally. Keep the precise return types of
    /// known overrides when available, and otherwise use the static top type
    /// rather than leaking `T.noreturn` into the base implementation.
    fn widen_overridable_noreturn(&self, key: &MethodKey, mut signature: MethodSig) -> MethodSig {
        let Some(resolved) = self.resolve_method_key(key) else {
            return signature;
        };
        let Some(state) = self.declarations.methods.get(&resolved) else {
            return signature;
        };
        if state.explicit
            || !state.return_terminates
            || !state.return_type.as_ref().is_some_and(Type::is_never)
        {
            return signature;
        }
        let Some(owner) = resolved.owner.as_deref() else {
            return signature;
        };

        let mut override_type = Type::Never;
        let mut found_override = false;
        for (candidate, candidate_state) in &self.declarations.methods {
            if candidate.singleton != resolved.singleton
                || candidate.name != resolved.name
                || candidate.owner.as_deref() == Some(owner)
            {
                continue;
            }
            let Some(candidate_owner) = candidate.owner.as_deref() else {
                continue;
            };
            if !self.nominal_subtype_names(nominal_name(candidate_owner), nominal_name(owner)) {
                continue;
            }
            found_override = true;
            let Some(return_type) = candidate_state.return_type.as_ref() else {
                signature.return_type = Type::union([Type::Nil, Type::Object]);
                return signature;
            };
            if return_type.is_any() {
                signature.return_type = Type::union([Type::Nil, Type::Object]);
                return signature;
            }
            if !return_type.is_never() {
                override_type = override_type.join(return_type);
            }
        }

        if found_override {
            signature.return_type = if override_type.is_never() {
                Type::union([Type::Nil, Type::Object])
            } else {
                override_type
            };
        }
        signature
    }

    fn private_call_allowed(&self, key: &MethodKey, environment: &Environment) -> bool {
        let Some(current) = environment.method_key.as_ref() else {
            return false;
        };
        let Some(current_owner) = current.owner.as_deref() else {
            return false;
        };
        let Some(resolved_owner) = self
            .resolve_method_key(key)
            .and_then(|resolved| resolved.owner)
        else {
            return false;
        };
        current_owner == resolved_owner
            || (!current.singleton && self.nominal_subtype(current_owner, &resolved_owner))
            || (current.singleton
                && key.singleton
                && self.nominal_subtype(current_owner, &resolved_owner))
    }

    fn call_terminates<'node, C: CallShape<'node>>(
        &self,
        call: &C,
        environment: &Environment,
        receiver_type: &Type,
        type_: &Type,
    ) -> bool {
        let name = call.name();
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
        self.declarations.methods.get(&key).is_some_and(|state| {
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
        self.declarations.methods.get(&target).is_some_and(|state| {
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
        if let Some(state) = self
            .declarations
            .methods
            .get(&key)
            .filter(|state| state.explicit)
        {
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
            let recursive_inferred = self
                .substitution_context
                .as_ref()
                .and_then(|current| self.resolve_method_key(current))
                .is_some_and(|current| {
                    current == key
                        && self
                            .declarations
                            .methods
                            .get(&current)
                            .is_some_and(|state| !state.explicit)
                });
            let state = self.declarations.methods.get_mut(&key)?;
            let mut changed = false;
            let positional_types = if state.accepts_keyword_rest || !state.keywords.is_empty() {
                &arguments.positional_types
            } else {
                &arguments.argument_types
            };
            // A direct recursive call often passes a value derived from the
            // current method parameter. Observing that provisional `Any`
            // argument would permanently poison the parameter summary before
            // an external call can provide concrete evidence.
            let recursive_arguments_concrete = !positional_types.iter().any(Type::contains_any)
                && arguments
                    .keyword_arguments
                    .iter()
                    .all(|argument| !argument.type_.contains_any());
            if (!recursive_inferred || recursive_arguments_concrete)
                && !arguments.forwards_arguments
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
            self.fixpoint.changed_methods.insert(key);
        }
        Some(signature)
    }

    /// `define_method` binds its block to instances of the receiver's class.
    /// Preserve that runtime fact when an inferred helper such as a test DSL
    /// forwards `&block`; otherwise a class-level declaration block is checked
    /// with the declaring class object as `self` instead of the eventual
    /// instance.
    fn observe_define_method_binding(
        &mut self,
        name: &str,
        arguments: &CallArguments<'_>,
        block: Option<&Node<'_>>,
        environment: &Environment,
    ) {
        if name != "define_method"
            || (block.is_none()
                && !arguments
                    .argument_nodes
                    .iter()
                    .any(|argument| argument.as_block_argument_node().is_some()))
        {
            return;
        }
        let Some(current) = environment.method_key.as_ref() else {
            return;
        };
        let Some(state) = self.declarations.methods.get_mut(current) else {
            return;
        };
        if !state.explicit && !state.binds_block_to_receiver {
            state.binds_block_to_receiver = true;
            self.fixpoint.changed_methods.insert(current.clone());
        }
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
        let previous_substitution_context = self.substitution_context.replace(key.clone());
        let block_signature = signature.block.as_ref().map(|block| {
            self.substitute_signature_type(
                block,
                receiver_type,
                &bindings,
                &signature.type_parameters,
            )
        });
        self.substitution_context = previous_substitution_context;
        let expected = block_signature
            .as_ref()
            .and_then(optional_proc_type)
            .and_then(|block| proc_parts(&block).map(|(parameters, _)| parameters.to_vec()))
            .unwrap_or_else(|| {
                self.declarations
                    .methods
                    .get(&key)
                    .map_or_else(Vec::new, MethodState::block_parameters)
            });
        let previous_expected_return = self.expected_return_type.take();
        let expected_block_return = block_signature
            .as_ref()
            .and_then(optional_proc_type)
            .and_then(|block| proc_parts(&block).map(|(_, result)| result.clone()));
        self.expected_return_type = expected_block_return.map(|expected| {
            if matches!(expected, Type::TypeVar(_)) {
                Self::literal_block_tuple_type(block).unwrap_or(expected)
            } else {
                expected
            }
        });
        let class_new_receiver = (key.name == "new"
            && key.singleton
            && key
                .owner
                .as_deref()
                .is_some_and(|owner| name_matches(owner, "Class")))
        .then(|| {
            arguments
                .argument_types
                .first()
                .filter(|argument| Self::class_object_instance_type(argument).is_some())
                .cloned()
        })
        .flatten();
        let binds_block_to_receiver = self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| state.binds_block_to_receiver);
        let bound_receiver = class_new_receiver
            .or_else(|| self.active_support_test_block_receiver(&key, receiver_type))
            .or_else(|| {
                block_signature
                    .as_ref()
                    .and_then(optional_proc_type)
                    .and_then(|block| proc_receiver(&block).cloned())
            })
            .or_else(|| {
                binds_block_to_receiver
                    .then(|| receiver_type.and_then(Self::class_object_instance_type))
                    .flatten()
            })
            .or_else(|| self.rails_initializer_block_receiver(&key, receiver_type))
            .or_else(|| self.rails_application_configure_block_receiver(&key, receiver_type))
            .or_else(|| self.rails_route_draw_block_receiver(&key, receiver_type))
            .or_else(|| self.active_support_ci_block_receiver(&key, receiver_type));
        let (block_type, passed_block_signature) = if block.as_block_argument_node().is_some() {
            if let Some(expected_signature) = block_signature.as_ref().and_then(optional_proc_type)
            {
                if block
                    .as_block_argument_node()
                    .and_then(|block| block.expression())
                    .and_then(|expression| expression.as_symbol_node())
                    .is_some()
                {
                    (
                        self.eval_symbol_passed_block(block, &expected_signature, environment),
                        None,
                    )
                } else {
                    let Some(expression_type) =
                        self.passed_block_expression_type(block, environment)
                    else {
                        // `&nil` is Ruby's spelling for omitting a block.
                        return None;
                    };
                    if let Some(signature) = Self::passed_block_signature(&expression_type) {
                        let return_type =
                            proc_parts(&signature).map_or(Type::Any, |(_, result)| result.clone());
                        (return_type, Some(signature))
                    } else {
                        (Type::Any, None)
                    }
                }
            } else {
                let Some(expression_type) = self.passed_block_expression_type(block, environment)
                else {
                    // `&nil` is Ruby's spelling for omitting a block.
                    return None;
                };
                if let Some(signature) = Self::passed_block_signature(&expression_type) {
                    let return_type =
                        proc_parts(&signature).map_or(Type::Any, |(_, result)| result.clone());
                    (return_type, Some(signature))
                } else {
                    (Type::Any, None)
                }
            }
        } else if matches!(
            key.name.as_str(),
            "define_method" | "define_singleton_method"
        ) {
            // These APIs consume the block as a method body rather than as a
            // callback.  Their core RBI supplies a generic block signature,
            // so handle the body here before the ordinary callback path can
            // accidentally retain the lexical module/class self.
            self.eval_dynamic_method_body(&key.name, block, environment);
            (Type::Any, None)
        } else {
            let block_type = if let Some(receiver) = bound_receiver.as_ref() {
                self.eval_bound_block_node(block, &expected, receiver, environment)
            } else {
                self.eval_block_node(block, &expected, environment)
            };
            (block_type, None)
        };
        self.expected_return_type = previous_expected_return;
        let mut checked_bindings =
            self.infer_type_parameter_bindings(signature, arguments, Some(&block_type));
        checked_bindings.extend(self.infer_generic_member_bindings(
            signature,
            arguments,
            receiver_type,
        ));
        let checked_block_signature = self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| state.explicit)
            .then(|| {
                let previous_substitution_context = self.substitution_context.replace(key.clone());
                let result = signature.block.as_ref().map(|block| {
                    self.substitute_signature_type(
                        block,
                        receiver_type,
                        &checked_bindings,
                        &signature.type_parameters,
                    )
                });
                self.substitution_context = previous_substitution_context;
                result
            })
            .flatten();
        if let Some(actual_block_signature) = passed_block_signature {
            if let Some(expected_block_signature) = checked_block_signature
                .as_ref()
                .and_then(optional_proc_type)
            {
                if !self.is_assignable(&actual_block_signature, &expected_block_signature) {
                    self.error(
                        block,
                        format!(
                            "Expected `{}` but found `{}` for block argument",
                            Self::block_type_description(&expected_block_signature),
                            Self::block_type_description(&actual_block_signature),
                        ),
                    );
                }
            }
        } else if let Some(block_signature) = checked_block_signature
            .as_ref()
            .and_then(optional_proc_type)
        {
            if let Some((_, expected_return)) = proc_parts(&block_signature) {
                if !expected_return.is_any()
                    && !expected_return.is_nil()
                    && !self.is_assignable(&block_type, &expected_return)
                {
                    self.check_assignable(block, &block_type, &expected_return);
                }
            }
        }
        if self
            .declarations
            .methods
            .get(&key)
            .is_some_and(|state| !state.explicit)
            && self
                .declarations
                .methods
                .get_mut(&key)
                .is_some_and(|state| state.observe_block_return(&block_type))
        {
            self.fixpoint.changed_methods.insert(key);
        }
        Some(block_type)
    }

    /// Rails initializers are stored as callbacks and later executed with
    /// `Rails::Initializable::Initializer#run`, which uses `instance_exec` on
    /// the engine or railtie instance. The generated Rails RBI does not encode
    /// that receiver binding, so recover it from the defining extension
    /// module when checking an initializer declaration block.
    fn rails_initializer_block_receiver(
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
    fn rails_application_configure_block_receiver(
        &self,
        key: &MethodKey,
        receiver_type: Option<&Type>,
    ) -> Option<Type> {
        (key.name == "configure")
            .then(|| receiver_type.filter(|type_| self.is_rails_application_instance(type_)))
            .flatten()
            .cloned()
    }

    fn is_rails_application_instance(&self, type_: &Type) -> bool {
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

    fn rails_application_instance_type(&self) -> Option<Type> {
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

    fn rails_route_draw_block_receiver(
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

    fn active_support_ci_block_receiver(
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
    fn active_support_test_block_receiver(
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

    fn eval_symbol_passed_block<'node>(
        &mut self,
        node: &Node<'node>,
        expected: &Type,
        environment: &mut Environment,
    ) -> Type {
        let Some(symbol) = node
            .as_block_argument_node()
            .and_then(|block| block.expression())
            .and_then(|expression| expression.as_symbol_node())
        else {
            return Type::Any;
        };
        let name = String::from_utf8_lossy(symbol.unescaped()).into_owned();
        let Some((parameters, _)) = proc_parts(expected) else {
            return Type::Any;
        };
        let Some(receiver) = parameters.first() else {
            return Type::Any;
        };
        let Some(key) = self.receiver_method_key(None, receiver, &name, environment) else {
            return Type::Any;
        };
        self.record_method_dependency(&key, environment);
        let Some(signature) = self.observe_call(&key, &CallArguments::default(), false) else {
            return Type::Any;
        };
        let owner = self
            .resolve_method_key(&key)
            .and_then(|resolved| resolved.owner)
            .unwrap_or_else(|| receiver.to_string());
        let method = format!("{owner}#{name}");

        // Symbol#to_proc consumes the first yielded value as the receiver;
        // all remaining yielded values are passed to the named method.
        let mut positional = Vec::new();
        let mut keywords = BTreeMap::<String, Type>::new();
        for argument in parameters.iter().skip(1) {
            if let Type::Named(shape, _) = argument {
                if shape.starts_with('{') && shape.ends_with('}') {
                    for keyword in signature.keywords.keys() {
                        if let Some(type_) = signature::parse_inline_record_field(shape, keyword) {
                            keywords.insert(keyword.clone(), type_);
                        }
                    }
                    if !keywords.is_empty() {
                        continue;
                    }
                }
            }
            positional.push(argument.clone());
        }

        if !signature.accepts_rest && positional.len() > signature.params.len() {
            self.error(
                node,
                format!(
                    "Too many positional arguments provided for method `{method}`. Expected: `{}`, got: `{}`",
                    signature.params.len(),
                    positional.len(),
                ),
            );
        }
        for (index, actual) in positional.iter().enumerate() {
            if let Some(expected) = signature.positional_type(index, positional.len()) {
                if !self.is_assignable(actual, expected) {
                    self.error(
                        node,
                        format!(
                            "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                        ),
                    );
                }
            }
        }
        for (name, parameter) in &signature.keywords {
            let Some(actual) = keywords.get(name) else {
                if parameter.required {
                    self.error(
                        node,
                        format!("Missing required keyword argument `{name}` for method `{method}`"),
                    );
                }
                continue;
            };
            if !self.is_assignable(actual, &parameter.type_) {
                self.error(
                    node,
                    format!(
                        "Expected `{}` but found `{actual}` for argument `{name}`",
                        parameter.type_
                    ),
                );
            }
        }
        if !signature.accepts_keyword_rest
            && keywords
                .keys()
                .any(|name| !signature.keywords.contains_key(name))
        {
            // Inline record parameters are only materialized for keywords
            // present in the called method's signature above.
        }
        self.substitute_signature_type(
            &signature.return_type,
            Some(receiver),
            &BTreeMap::new(),
            &signature.type_parameters,
        )
    }

    fn select_overload(
        &self,
        overloads: &[MethodSig],
        arguments: &CallArguments<'_>,
        has_block: bool,
    ) -> Option<MethodSig> {
        let matching = overloads
            .iter()
            .enumerate()
            .filter(|(_, signature)| self.signature_accepts_arguments(signature, arguments))
            .collect::<Vec<_>>();
        let block_preference = |signature: &MethodSig| {
            if has_block == signature.block.is_some() {
                0
            } else {
                1
            }
        };
        matching
            .into_iter()
            .min_by_key(|(index, signature)| {
                let positional_count =
                    if !signature.keywords.is_empty() || signature.accepts_keyword_rest {
                        arguments.positional_types.len()
                    } else {
                        arguments.argument_types.len()
                    };
                (
                    block_preference(signature),
                    signature.params.len().saturating_sub(positional_count),
                    *index,
                )
            })
            .map(|(_, signature)| signature.clone())
    }

    fn signature_accepts_arguments(
        &self,
        signature: &MethodSig,
        arguments: &CallArguments<'_>,
    ) -> bool {
        if !self.signature_shape_accepts_arguments(signature, arguments) {
            return false;
        }
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
            self.is_assignable(actual, &expected) || matches!(expected, Type::TypeVar(_))
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
                            || matches!(expected, Type::TypeVar(_))
                    })
                    || signature.accepts_keyword_rest
            })
        {
            return false;
        }
        true
    }

    fn signature_shape_accepts_arguments(
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
        true
    }

    fn record_method_dependency(&mut self, key: &MethodKey, environment: &Environment) {
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
    fn widen_recursive_call_return(
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

    fn resolve_method_key(&self, key: &MethodKey) -> Option<MethodKey> {
        if let Some(resolved) = self.method_resolution_cache.borrow().get(key) {
            return resolved.clone();
        }
        let resolved = self.resolve_method_key_inner(key, &mut BTreeSet::new());
        self.method_resolution_cache
            .borrow_mut()
            .insert(key.clone(), resolved.clone());
        resolved
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

    fn infer_initializer_call<'node>(
        &mut self,
        node: &Node<'node>,
        owner: &str,
        arguments: &CallArguments<'node>,
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
            let _ = self.invoke_signature(
                node,
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

    fn observe_struct_constructor(&mut self, owner: &str, arguments: &CallArguments<'_>) {
        let Some(fields) = self.declarations.struct_fields.get(owner).cloned() else {
            return;
        };
        for (field, actual) in fields.iter().zip(&arguments.positional_types) {
            let key = (owner.to_owned(), field.clone());
            let next = self
                .declarations
                .struct_field_types
                .get(&key)
                .map_or_else(|| actual.clone(), |current| current.join(actual));
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

    fn struct_field_type(
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

    fn implicit_method_key(&self, name: &str, environment: &Environment) -> MethodKey {
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

    fn receiver_method_key<'node>(
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

    fn dynamic_ivar_keys(
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

    fn begin_method_evaluation(&mut self, method: &MethodKey) {
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

    fn record_shared_read(&mut self, key: SharedKey, environment: &Environment) {
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

    fn observe_ivar(
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

    fn dynamic_instance_variable_name(&self, node: &Node<'_>) -> Option<String> {
        let name = node
            .as_symbol_node()
            .map(|symbol| String::from_utf8_lossy(symbol.unescaped()).into_owned())
            .or_else(|| {
                node.as_string_node()
                    .map(|string| String::from_utf8_lossy(string.unescaped()).into_owned())
            })?;
        name.starts_with('@').then_some(name)
    }

    fn observe_dynamic_ivar(&mut self, key: IvarKey, actual: &Type) {
        let next = self
            .ivars
            .get(&key)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.ivars.get(&key) != Some(&next) {
            self.ivars.insert(key.clone(), next);
            self.fixpoint.changed_shared.insert(SharedKey::Ivar(key));
        }
    }

    fn eval_dynamic_instance_variable_call(
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

    fn inferred_accessor_ivar_type(
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
            self.fixpoint.changed_shared.insert(SharedKey::Ivar(key));
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

    fn eval_dynamic_struct_block<'node>(
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

    fn observe_constant(&mut self, environment: &Environment, name: String, actual: &Type) {
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
            self.fixpoint
                .changed_shared
                .insert(SharedKey::ClassVar(key));
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

    fn observe_global(&mut self, name: String, actual: &Type) {
        let next = self
            .globals
            .get(&name)
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if self.globals.get(&name) != Some(&next) {
            self.globals.insert(name.clone(), next);
            self.fixpoint.changed_shared.insert(SharedKey::Global(name));
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

    fn observe_extend_hook<'node>(
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

    fn observe_extend_hook_for_base<'node>(
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
                self.fixpoint
                    .changed_methods
                    .extend(self.declarations.methods.keys().cloned());
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

    fn observe_include_hook<'node>(
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

    fn observe_include_hook_for_base<'node>(
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
                self.fixpoint
                    .changed_methods
                    .extend(self.declarations.methods.keys().cloned());
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
            "is_a?" | "kind_of?" | "instance_of?" => Type::bool(),
            "require" | "require_relative" | "load" => Type::bool(),
            "raise" | "fail" | "abort" | "exit" | "exit!" => Type::Never,
            "Integer" => Type::Integer,
            "Float" => Type::Float,
            "String" | "__dir__" => Type::String,
            "Symbol" => Type::Symbol,
            "Array" => argument_types.first().map_or_else(
                || Type::Array(Box::new(Type::Any)),
                |type_| Type::Array(Box::new(self.array_coercion_element_type(type_))),
            ),
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
                    if let Some(element) = Self::dynamic_splat_element_type(splat_type) {
                        if !self.is_assignable(&element, &expected) {
                            self.check_assignable(node, &element, &expected);
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
        if arguments.has_dynamic_keyword_splat && !signature.accepts_keyword_rest {
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

        if self.checking_initializer {
            if argument_types.len() < signature.required_params {
                self.error(node, "Not enough arguments provided");
            } else if !signature.accepts_rest && argument_types.len() > signature.params.len() {
                self.error(node, "Too many arguments provided");
            }
            if missing_keywords {
                for (name, parameter) in &signature.keywords {
                    if parameter.required && !provided_keywords.contains(name.as_str()) {
                        self.error(node, format!("Missing required keyword argument `{name}`"));
                    }
                }
            }
            if self.initializer_requires_block
                && signature
                    .block
                    .as_ref()
                    .is_some_and(|block| matches!(block, Type::Proc(_, _) | Type::BoundProc { .. }))
                && !self.initializer_has_block
            {
                self.error(node, "`initialize` requires a block parameter");
            }
        } else if name == "new"
            && positional_error
            && argument_types.len() < signature.required_params
        {
            if let Some(owner) = receiver_type.and_then(Self::class_object_owner) {
                self.error(
                    node,
                    format!("Not enough arguments provided for method `{owner}.new`"),
                );
            } else {
                self.error(node, "Wrong number of arguments for `new`");
            }
        } else if positional_error || missing_keywords || unknown_keyword {
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
                if arguments.has_dynamic_keyword_splat
                    && arguments
                        .argument_nodes
                        .get(*argument_index)
                        .is_some_and(|argument| argument.as_keyword_hash_node().is_some())
                {
                    continue;
                }
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
            let return_type = self.substitute_signature_type(
                &signature.return_type,
                receiver_type,
                &type_parameter_bindings,
                &signature.type_parameters,
            );
            if name == "flat_map" {
                if let Some(block_return_type) = block_return_type {
                    return Type::Array(Box::new(self.flat_map_element_type(block_return_type)));
                }
            }
            if matches!(name, "sort" | "sort_by") {
                if let Some(Type::Hash(key, value)) = receiver_type {
                    return Type::Array(Box::new(Type::Tuple(vec![
                        key.as_ref().clone(),
                        value.as_ref().clone(),
                    ])));
                }
            }
            if name == "to_h" {
                if let Some(block_return_type) = block_return_type {
                    if let Some((key, value)) = Self::pair_types(block_return_type) {
                        return Type::Hash(Box::new(key), Box::new(value));
                    }
                }
                if let Some(receiver_type) = receiver_type {
                    if let Some((key, value)) = Self::pair_types(receiver_type) {
                        return Type::Hash(Box::new(key), Box::new(value));
                    }
                }
            }
            if name == "grep" {
                if let Some(expected) = arguments
                    .argument_types
                    .first()
                    .and_then(Self::class_object_value_type)
                {
                    let element = match &return_type {
                        Type::Array(element) => Some(element.as_ref()),
                        Type::Named(class, arguments)
                            if arguments.len() == 1 && name_matches(class, "Array") =>
                        {
                            arguments.first()
                        }
                        _ => None,
                    };
                    if let Some(element) = element {
                        return Type::Array(Box::new(self.meet_predicate_type(element, &expected)));
                    }
                }
            }
            return_type
        }
    }
}
