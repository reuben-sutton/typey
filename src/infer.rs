use crate::cfg;
use crate::diagnostic::{Diagnostic, Severity};
use crate::directives::{effective_typed_mode, is_typed_ignore, typed_mode, TypedMode};
use crate::hir;
use crate::prism;
use crate::signature::{self, AssertionKind, MethodSig};
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
mod context;
mod control_flow;
mod declarations;
mod dispatch;
mod environment;
mod exceptions;
mod fixpoint;
mod flow;
mod framework_hooks;
mod hash_shape;
mod intrinsics;
mod keys;
mod legacy_bridge;
mod legacy_eval;
mod legacy_methods;
mod legacy_patterns;
mod method_lookup;
mod method_state;
mod method_types;
mod owned_blocks;
mod owned_definitions;
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
use context::ProgramContext;
use declarations::{AccessorKind, DeclarationState, MethodRegistrar, Visibility};
pub use environment::Environment;
use environment::PredicateAlias;
use fixpoint::FixpointState;
use flow::{Eval, Flow, FlowKind, OutcomeTypes};
use keys::{
    ivar_refinement_key, name_matches, nominal_name, ClassVarKey, IvarKey, MethodKey, SharedKey,
};
use method_state::{BlockReceiverBinding, MethodState};
use method_types::{
    apply_parameter_shape, optional_proc_type, proc_parts, proc_receiver, ParameterShape,
};
use source::{ReportingState, SourceSite};

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
    let program = ProgramContext::new(bytes, hir_program, cfg_graphs, annotations);
    let analyzer = Analyzer {
        program,
        config,
        declarations: DeclarationState::default(),
        method_resolution_cache: RefCell::new(BTreeMap::new()),
        global_name_cache: RefCell::new(HashMap::new()),
        instance_self_type_cache: RefCell::new(HashMap::new()),
        ivars: BTreeMap::new(),
        provisional_ivars: BTreeSet::new(),
        class_vars: BTreeMap::new(),
        globals: BTreeMap::new(),
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
        reporting: ReportingState::new(diagnostics.clone()),
        cfg_transfer_bodies: 0,
        cfg_transfer_calls: 0,
        cfg_transfer_assignments: 0,
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
    program: ProgramContext<'src>,
    config: CheckerConfig,
    declarations: DeclarationState,
    method_resolution_cache: RefCell<BTreeMap<MethodKey, Option<MethodKey>>>,
    global_name_cache: RefCell<HashMap<String, String>>,
    instance_self_type_cache: RefCell<HashMap<String, Type>>,
    ivars: BTreeMap<IvarKey, Type>,
    provisional_ivars: BTreeSet<IvarKey>,
    class_vars: BTreeMap<ClassVarKey, Type>,
    globals: BTreeMap<String, Type>,
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
    reporting: ReportingState,
    cfg_transfer_bodies: usize,
    cfg_transfer_calls: usize,
    cfg_transfer_assignments: usize,
    cfg_transfer_values: usize,
    cfg_transfer_fallbacks: CfgFallbackCounters,
}
