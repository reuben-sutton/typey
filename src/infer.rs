use crate::cfg;
use crate::diagnostic::{Diagnostic, Severity};
use crate::directives::{effective_typed_mode, is_typed_ignore, typed_mode, TypedMode};
use crate::hir;
use crate::prism;
use crate::signature::{self, AnnotationTable, AssertionKind, MethodSig};
use crate::types::Type;
use ruby_prism::{ArgumentsNode, CallNode, Node, Visit};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

mod arguments;
mod assignments;
mod blocks;
mod builtins;
mod call_dispatch;
mod call_types;
mod calls;
mod case_flow;
mod cfg_state;
mod cfg_transfer;
mod control_flow;
mod declarations;
mod dispatch;
mod environment;
mod exceptions;
mod fixpoint;
mod flow;
mod framework_hooks;
mod intrinsics;
mod keys;
mod legacy_bridge;
mod legacy_eval;
mod legacy_methods;
mod method_lookup;
mod method_state;
mod method_types;
mod owned_blocks;
mod predicate_flow;
mod registration;
mod runner;
mod shared_state;
mod signature_calls;
mod source;
mod type_resolution;
mod type_system;

use call_types::{
    hir_call_argument_inputs, prism_call_argument_inputs, CallArgumentEvaluation,
    CallArgumentInput, CallArguments, CallSite, HirCallView, IndexAccess, KeywordArgument,
    KeywordArgumentInput, OwnedCallInput,
};
use cfg_transfer::{CfgFallbackCounters, CfgFallbackKind};
use declarations::{AccessorKind, DeclarationState, MethodRegistrar, Visibility};
pub use environment::Environment;
use environment::PredicateAlias;
use fixpoint::FixpointState;
use flow::{Eval, Flow, FlowKind, OutcomeTypes};
use keys::{
    ivar_refinement_key, name_matches, nominal_name, ClassVarKey, IvarKey, MethodKey, SharedKey,
};
use method_state::MethodState;
use method_types::{
    apply_parameter_shape, optional_proc_type, proc_parts, proc_receiver, ParameterShape,
};
use source::SourceSite;

const DEBUG_NODE_INTERVAL: usize = 1_000;

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
    /// Compile owned HIR bodies into CFGs for the in-progress differential
    /// migration. The default remains off until CFG transfer replaces the
    /// recursive evaluator for all supported bodies.
    pub enable_cfg: bool,
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            strictness: Strictness::Ignore,
            debug: false,
            enable_cfg: false,
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
    let cfg_graphs = config
        .enable_cfg
        .then(|| Arc::<[cfg::Cfg]>::from(cfg::lower::build_all_for_index(&hir_program)));
    let cfg_index = cfg_graphs
        .as_deref()
        .map(|graphs| cfg::CfgIndex::from_graphs(&hir_program, graphs));
    let mut hir_call_ids = HashMap::new();
    let mut hir_assignment_ids = HashMap::new();
    let mut hir_value_ids = HashMap::new();
    let hir_body_ids = hir_program
        .bodies
        .iter()
        .enumerate()
        .map(|(index, body)| {
            (
                (body.span.start as usize, body.span.end as usize),
                hir::BodyId(index as u32),
            )
        })
        .collect::<HashMap<_, _>>();
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
            hir::ExprKind::Nil | hir::ExprKind::Literal(_) | hir::ExprKind::Read(_) => {
                hir_value_ids
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
        cfg_index,
        cfg_graphs,
        hir_call_ids,
        hir_assignment_ids,
        hir_value_ids,
        hir_body_ids,
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
        cfg_transfer_bodies: 0,
        cfg_transfer_calls: 0,
        cfg_transfer_assignments: 0,
        cfg_transfer_conditionals: 0,
        cfg_transfer_loops: 0,
        cfg_transfer_values: 0,
        cfg_transfer_fallbacks: CfgFallbackCounters::default(),
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
    cfg_index: Option<cfg::CfgIndex>,
    cfg_graphs: Option<Arc<[cfg::Cfg]>>,
    hir_call_ids: HashMap<(usize, usize), hir::ExprId>,
    hir_assignment_ids: HashMap<(usize, usize), hir::ExprId>,
    hir_value_ids: HashMap<(usize, usize), hir::ExprId>,
    hir_body_ids: HashMap<(usize, usize), hir::BodyId>,
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
    cfg_transfer_bodies: usize,
    cfg_transfer_calls: usize,
    cfg_transfer_assignments: usize,
    cfg_transfer_conditionals: usize,
    cfg_transfer_loops: usize,
    cfg_transfer_values: usize,
    cfg_transfer_fallbacks: CfgFallbackCounters,
}

impl<'src> Analyzer<'src> {
    fn normal_type(result: Eval) -> Type {
        result.normal_type.unwrap_or(Type::Never)
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
}
