use crate::cfg;
use crate::diagnostic::{Diagnostic, Severity};
use crate::directives::{effective_typed_mode, is_typed_ignore, typed_mode, TypedMode};
use crate::hir;
use crate::prism;
use crate::signature::{self, AnnotationTable, AssertionKind, MethodSig};
use crate::types::Type;
use ruby_prism::{
    ArgumentsNode, CallNode, DefNode, IfNode, Node, ParametersNode, UnlessNode, Visit,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

mod arguments;
mod blocks;
mod builtins;
mod call_types;
mod calls;
mod cfg_state;
mod cfg_transfer;
mod control_flow;
mod declarations;
mod dispatch;
mod environment;
mod fixpoint;
mod flow;
mod legacy_bridge;
mod legacy_eval;
mod method_lookup;
mod method_state;
mod method_types;
mod owned_blocks;
mod predicate_flow;
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
use declarations::{DeclarationState, MethodRegistrar};
pub use environment::Environment;
use environment::PredicateAlias;
use fixpoint::FixpointState;
use flow::{Eval, Flow, FlowKind, OutcomeTypes};
use method_state::MethodState;
use method_types::{
    apply_parameter_shape, optional_proc_type, proc_parts, proc_receiver, ParameterShape,
};
use source::SourceSite;

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
        self.record_at(
            SourceSite::new(start, end),
            type_,
            self.report && Self::is_send_node(node),
            untyped_origin,
        )
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
        self.error_at(SourceSite::new(start, end), message);
    }

    fn note<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.report || self.suppress_diagnostics {
            return;
        }
        let (start, end) = prism::span(node);
        self.note_at(SourceSite::new(start, end), message);
    }

    fn eval_call_result<'node>(
        &mut self,
        node: &Node<'node>,
        call: &HirCallView<'node>,
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
        call: CallNode<'node>,
        target: &hir::AssignTarget,
        value: hir::ExprId,
        environment: &mut Environment,
    ) -> Eval {
        // Keep the assignment as an owned HIR assignment, but reuse the
        // established setter protocol for its runtime send. The synthetic
        // call is an evaluator adapter only: its receiver and argument shape
        // come from the HIR target, while the source Prism node remains solely
        // the child-expression bridge used by `HirCallView`.
        let (name, receiver, arguments) = match target {
            hir::AssignTarget::Attribute { receiver, name } => (
                format!("{}=", name.as_str()),
                hir::Receiver::Explicit(*receiver),
                vec![hir::Argument::Positional(value)],
            ),
            hir::AssignTarget::Index {
                receiver,
                arguments,
            } => {
                let mut arguments = arguments.clone();
                arguments.push(hir::Argument::Positional(value));
                (
                    "[]=".to_owned(),
                    hir::Receiver::Explicit(*receiver),
                    arguments,
                )
            }
            _ => return Eval::value(self.record(node, Type::Any)),
        };
        let view = HirCallView {
            call: hir::Call {
                receiver,
                name: hir::Name::new(name),
                arguments,
                argument_groups: Vec::new(),
                argument_spans: Vec::new(),
                block: None,
                safe_navigation: false,
                span: hir::Span::new(
                    hir::FileId(0),
                    prism::span(node).0 as u32,
                    prism::span(node).1 as u32,
                ),
            },
            prism_call: call,
        };
        self.eval_call_result(node, &view, environment)
    }

    fn eval_hir_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        target: hir::AssignTarget,
        value_id: hir::ExprId,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        debug_assert!(self.hir_program.expression(value_id).is_some());
        let value_node = self
            .assignment_value_node(node)
            .expect("lowered assignment must retain its value expression");
        match target {
            hir::AssignTarget::Attribute { receiver, name } => {
                let receiver_node = self
                    .assignment_receiver_node(node)
                    .expect("lowered attribute assignment must retain its receiver");
                match operator {
                    hir::AssignOperator::Set => {
                        let call = node
                            .as_call_node()
                            .expect("plain attribute assignment is a call node");
                        self.eval_hir_set_assignment(
                            node,
                            call,
                            &hir::AssignTarget::Attribute { receiver, name },
                            value_id,
                            environment,
                        )
                    }
                    hir::AssignOperator::And => self.eval_call_assignment(
                        node,
                        receiver_node,
                        name.as_str(),
                        &format!("{}=", name.as_str()),
                        value_node,
                        CallAssignmentKind::And,
                        environment,
                    ),
                    hir::AssignOperator::Or => self.eval_call_assignment(
                        node,
                        receiver_node,
                        name.as_str(),
                        &format!("{}=", name.as_str()),
                        value_node,
                        CallAssignmentKind::Or,
                        environment,
                    ),
                    hir::AssignOperator::Binary(operator) => self.eval_call_assignment(
                        node,
                        receiver_node,
                        name.as_str(),
                        &format!("{}=", name.as_str()),
                        value_node,
                        CallAssignmentKind::Operator(operator.as_str().to_owned()),
                        environment,
                    ),
                }
            }
            hir::AssignTarget::Index {
                receiver: hir_receiver,
                arguments: hir_arguments,
            } => match operator {
                hir::AssignOperator::Set => {
                    let call = node
                        .as_call_node()
                        .expect("plain index assignment is a call node");
                    self.eval_hir_set_assignment(
                        node,
                        call,
                        &hir::AssignTarget::Index {
                            receiver: hir_receiver,
                            arguments: hir_arguments,
                        },
                        value_id,
                        environment,
                    )
                }
                operator => {
                    let receiver = self
                        .assignment_receiver_node(node)
                        .expect("lowered index assignment must retain its receiver");
                    let arguments = self
                        .assignment_index_arguments(node)
                        .expect("lowered index assignment must retain its arguments");
                    let kind = match operator {
                        hir::AssignOperator::And => IndexAssignmentKind::And,
                        hir::AssignOperator::Or => IndexAssignmentKind::Or,
                        hir::AssignOperator::Binary(operator) => {
                            IndexAssignmentKind::Operator(operator.as_str().to_owned())
                        }
                        hir::AssignOperator::Set => unreachable!("handled above"),
                    };
                    self.eval_index_assignment(
                        node,
                        receiver,
                        arguments,
                        &hir_arguments,
                        value_node,
                        kind,
                        environment,
                    )
                }
            },
            hir::AssignTarget::Local(local) => {
                let name = self
                    .hir_program
                    .local_name(local)
                    .expect("lowered local target must have a spelling")
                    .as_str()
                    .to_owned();
                self.eval_hir_local_assignment(node, name, value_node, operator, environment)
            }
            hir::AssignTarget::InstanceVariable(name) => self.eval_hir_instance_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
            hir::AssignTarget::ClassVariable(name) => self.eval_hir_class_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
            hir::AssignTarget::Global(name) => self.eval_hir_global_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
            hir::AssignTarget::Constant(name) => self.eval_hir_constant_assignment(
                node,
                name.as_str(),
                value_node,
                operator,
                environment,
            ),
        }
    }

    fn eval_hir_local_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: String,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                if let Some(alias) = self.predicate_alias_for_value(&value_node, environment) {
                    environment.bind_predicate_alias(name.clone(), type_.clone(), alias);
                } else {
                    environment.bind(name.clone(), type_.clone());
                }
                if value_node
                    .as_array_node()
                    .is_some_and(|array| array.elements().is_empty())
                    && matches!(&type_, Type::Array(element) if element.is_any())
                {
                    environment.open_array_locals.insert(name);
                }
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let result = self.eval_compound_assignment(
                    environment.get(&name),
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    environment.bind(name.clone(), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                let result =
                    self.eval_and_assignment(environment.get(&name), &value_node, environment);
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    environment.bind(name.clone(), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                let current = environment.get(&name);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = Self::normal_type(self.eval_node(&value_node, environment));
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared =
                    self.apply_inline_assertion_in_environment(node, actual, environment);
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
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_instance_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion_in_environment(node, actual, environment);
                let type_ =
                    self.preserve_typed_empty_array_ivar(environment, name, &value_node, type_);
                let provisional = value_node
                    .as_local_variable_read_node()
                    .is_some_and(|local| {
                        environment.is_provisional(&prism::constant_name(local.name()))
                    });
                self.observe_ivar(environment, name.to_owned(), &type_, provisional);
                environment.bind(ivar_refinement_key(name), type_.clone());
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let current = self.ivar_type(environment, name);
                let result = self.eval_compound_assignment(
                    current,
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    self.observe_ivar(environment, name.to_owned(), &type_, false);
                    environment.bind(ivar_refinement_key(name), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                let current = self.ivar_type(environment, name);
                let result = self.eval_and_assignment(current, &value_node, environment);
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ =
                        self.apply_inline_assertion_in_environment(node, type_, environment);
                    self.observe_ivar(environment, name.to_owned(), &type_, false);
                    environment.bind(ivar_refinement_key(name), type_.clone());
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                let current = self.ivar_type(environment, name);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = Self::normal_type(self.eval_node(&value_node, environment));
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared =
                    self.apply_inline_assertion_in_environment(node, actual, environment);
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared.clone()
                };
                self.observe_ivar(environment, name.to_owned(), &declared, false);
                environment.bind(ivar_refinement_key(name), type_.clone());
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_class_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.to_owned(), &type_);
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let current = self.class_var_type(environment, name);
                let result = self.eval_compound_assignment(
                    current,
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_class_var(environment, name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                let current = self.class_var_type(environment, name);
                let result = self.eval_and_assignment(current, &value_node, environment);
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_class_var(environment, name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                let current = self.class_var_type(environment, name);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = Self::normal_type(self.eval_node(&value_node, environment));
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared = self.apply_inline_assertion(node, actual);
                self.observe_class_var(environment, name.to_owned(), &declared);
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared
                };
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_global_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let type_ = self.apply_inline_assertion(node, actual);
                self.observe_global(name.to_owned(), &type_);
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                self.record_shared_read(SharedKey::Global(name.to_owned()), environment);
                let result = self.eval_compound_assignment(
                    self.globals.get(name).cloned().unwrap_or(Type::Any),
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_global(name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::And => {
                self.record_shared_read(SharedKey::Global(name.to_owned()), environment);
                let result = self.eval_and_assignment(
                    self.globals.get(name).cloned().unwrap_or(Type::Any),
                    &value_node,
                    environment,
                );
                let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
                let normal_type = normal_type.map(|type_| {
                    let type_ = self.apply_inline_assertion(node, type_);
                    self.observe_global(name.to_owned(), &type_);
                    type_
                });
                let mut result = Eval::from_parts(normal_type, abrupt, flow);
                result.type_ = self.record(node, result.type_.clone());
                result
            }
            hir::AssignOperator::Or => {
                self.record_shared_read(SharedKey::Global(name.to_owned()), environment);
                let current = self.globals.get(name).cloned().unwrap_or(Type::Any);
                let previous = self.defer_inline_assertions;
                self.defer_inline_assertions = true;
                let right = Self::normal_type(self.eval_node(&value_node, environment));
                self.defer_inline_assertions = previous;
                let actual = current.truthy_part().join(&right);
                let declared = self.apply_inline_assertion(node, actual);
                self.observe_global(name.to_owned(), &declared);
                let type_ = if right.without(&Type::Nil) == right {
                    declared.without(&Type::Nil)
                } else {
                    declared
                };
                Eval::value(self.record(node, type_))
            }
        }
    }

    fn eval_hir_constant_assignment<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        value_node: Node<'node>,
        operator: hir::AssignOperator,
        environment: &mut Environment,
    ) -> Eval {
        match operator {
            hir::AssignOperator::Set => {
                let actual = Self::normal_type(self.eval_node(&value_node, environment));
                let struct_type = self.struct_subclass_type(environment, &value_node, name);
                if let Some(struct_type) = struct_type.as_ref() {
                    self.eval_dynamic_struct_block(&value_node, struct_type, environment);
                }
                let type_ = self.apply_inline_assertion(node, struct_type.unwrap_or(actual));
                self.observe_constant(environment, name.to_owned(), &type_);
                Eval::value(self.record(node, type_))
            }
            hir::AssignOperator::Binary(operator) => {
                let current = self.constant_type(environment, name);
                let result = self.eval_compound_assignment(
                    current,
                    operator.as_str(),
                    &value_node,
                    environment,
                );
                self.finish_hir_constant_operation(node, name, result, environment)
            }
            hir::AssignOperator::And => {
                let current = self.constant_type(environment, name);
                let result = self.eval_and_assignment(current, &value_node, environment);
                self.finish_hir_constant_operation(node, name, result, environment)
            }
            hir::AssignOperator::Or => {
                let current = self.constant_type(environment, name);
                let result = self.eval_or_assignment(current, &value_node, environment);
                self.finish_hir_constant_operation(node, name, result, environment)
            }
        }
    }

    fn finish_hir_constant_operation<'node>(
        &mut self,
        node: &Node<'node>,
        name: &str,
        result: Eval,
        environment: &mut Environment,
    ) -> Eval {
        let (normal_type, abrupt, flow) = (result.normal_type, result.abrupt, result.flow);
        let normal_type = normal_type.map(|type_| self.apply_inline_assertion(node, type_));
        if let Some(type_) = normal_type.as_ref() {
            self.observe_constant(environment, name.to_owned(), type_);
        }
        let mut result = Eval::from_parts(normal_type, abrupt, flow);
        result.type_ = self.record(node, result.type_.clone());
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
            if self.config.enable_cfg {
                self.hir_body_ids
                    .get(&prism::span(node))
                    .copied()
                    .and_then(|body_id| {
                        self.eval_cfg_body(&body, body_id, &mut method_environment, true)
                    })
                    .unwrap_or_else(|| self.eval_node(&body, &mut method_environment))
            } else {
                self.eval_node(&body, &mut method_environment)
            }
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
        hir_call: Option<&hir::Call>,
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
                argument_sites: Vec::new(),
                argument_types: types,
                argument_indices: Vec::new(),
                positional_indices: Vec::new(),
                positional_types,
                keyword_arguments: Vec::new(),
                keyword_hash_indices: Vec::new(),
                has_keyword_splat: false,
                has_dynamic_positional_splat: false,
                dynamic_positional_splat_types: Vec::new(),
                has_dynamic_keyword_splat: false,
                has_unknown_positional_splat: false,
                has_unknown_keyword_splat: false,
                forwards_arguments: true,
            }
        } else {
            let argument_inputs = if let Some(call) = hir_call {
                hir_call_argument_inputs(&call.arguments, arguments)
            } else {
                prism_call_argument_inputs(arguments)
            };
            self.evaluate_call_arguments(argument_inputs, environment)
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

    fn call_terminates<'node>(
        &self,
        call: &HirCallView<'node>,
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
        self.eval_symbol_passed_block_named(
            Some(node),
            SourceSite::from_prism_span(prism::span(node)),
            &name,
            expected,
            environment,
        )
    }

    fn eval_symbol_passed_block_named(
        &mut self,
        node: Option<&Node<'_>>,
        site: SourceSite,
        name: &str,
        expected: &Type,
        environment: &mut Environment,
    ) -> Type {
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
            self.error_at_or_node(
                node,
                site,
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
                    self.error_at_or_node(
                        node,
                        site,
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
                    self.error_at_or_node(
                        node,
                        site,
                        format!("Missing required keyword argument `{name}` for method `{method}`"),
                    );
                }
                continue;
            };
            if !self.is_assignable(actual, &parameter.type_) {
                self.error_at_or_node(
                    node,
                    site,
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

    fn error_at_or_node(&mut self, node: Option<&Node<'_>>, site: SourceSite, message: String) {
        if let Some(node) = node {
            self.error(node, message);
        } else {
            self.error_at(site, message);
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
}
