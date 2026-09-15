//! Source locations used by inference paths that no longer need parser nodes.

use super::{strictness_rank, Analyzer, Environment, InferredType, Strictness, UntypedOrigin};
use crate::diagnostic::Diagnostic;
use crate::hir;
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeMap;

fn range_containing(ranges: &[(usize, usize)], offset: usize) -> Option<(usize, usize)> {
    let index = ranges.partition_point(|(_, end)| *end <= offset);
    ranges
        .get(index)
        .copied()
        .filter(|(start, end)| *start <= offset && offset < *end)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SourceSite {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) expression: Option<hir::ExprId>,
}

/// Diagnostics and source-level products of an analysis pass.
///
/// Keeping this state together makes publication a boundary rather than a set
/// of unrelated fields on `Analyzer`. Recursive evaluation and owned CFG
/// transfer can both record through the same sink while the runner swaps
/// reporting mode between seed, fixpoint, and final passes.
#[derive(Clone, Debug)]
pub(super) struct ReportingState {
    pub(super) report: bool,
    pub(super) suppress_diagnostics: bool,
    pub(super) diagnostics: Vec<Diagnostic>,
    pub(super) preserve_duplicate_diagnostics: BTreeMap<(usize, usize, String), usize>,
    pub(super) types: Vec<InferredType>,
    pub(super) untyped_origins: BTreeMap<(usize, usize), UntypedOrigin>,
}

impl ReportingState {
    pub(super) fn new(diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            report: true,
            suppress_diagnostics: false,
            diagnostics,
            preserve_duplicate_diagnostics: BTreeMap::new(),
            types: Vec::new(),
            untyped_origins: BTreeMap::new(),
        }
    }
}

impl SourceSite {
    pub(super) const fn new(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            expression: None,
        }
    }

    pub(super) const fn from_prism_span(span: (usize, usize)) -> Self {
        Self::new(span.0, span.1)
    }

    pub(super) const fn from_span(span: hir::Span, expression: Option<hir::ExprId>) -> Self {
        Self {
            start: span.start as usize,
            end: span.end as usize,
            expression,
        }
    }
}

impl<'src> Analyzer<'src> {
    fn contains_block_return_placeholder(type_: &Type) -> bool {
        match type_ {
            Type::TypeVar(name) => name.starts_with("$block_return:"),
            Type::Named(_, arguments) => arguments
                .iter()
                .any(Self::contains_block_return_placeholder),
            Type::Array(element) => Self::contains_block_return_placeholder(element),
            Type::Hash(key, value) => {
                Self::contains_block_return_placeholder(key)
                    || Self::contains_block_return_placeholder(value)
            }
            Type::Tuple(elements) | Type::Union(elements) | Type::Intersection(elements) => {
                elements.iter().any(Self::contains_block_return_placeholder)
            }
            Type::Proc(parameters, result) => {
                parameters
                    .iter()
                    .any(Self::contains_block_return_placeholder)
                    || Self::contains_block_return_placeholder(result)
            }
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => {
                Self::contains_block_return_placeholder(receiver)
                    || parameters
                        .iter()
                        .any(Self::contains_block_return_placeholder)
                    || Self::contains_block_return_placeholder(result)
            }
            Type::Any
            | Type::Anything
            | Type::Never
            | Type::Nil
            | Type::True
            | Type::False
            | Type::Integer
            | Type::Float
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::AttachedClass
            | Type::AttachedClassOf(_) => false,
        }
    }

    /// Convert internal inference placeholders to types suitable for callers.
    ///
    /// Forwarded unannotated blocks need a symbolic result while a method is
    /// being solved: the result belongs to the eventual call site's block,
    /// not to the method definition. That symbol is useful inside the
    /// fixpoint, but it is not a type parameter that a caller can act on.
    /// Never expose it through the public per-expression type stream.
    fn published_type(type_: &Type) -> Type {
        if !Self::contains_block_return_placeholder(type_) {
            return type_.clone();
        }
        match type_ {
            Type::TypeVar(name) if name.starts_with("$block_return:") => Type::Anything,
            Type::Named(name, arguments) => Type::Named(
                name.clone(),
                arguments.iter().map(Self::published_type).collect(),
            ),
            Type::Array(element) => Type::Array(Box::new(Self::published_type(element))),
            Type::Hash(key, value) => Type::Hash(
                Box::new(Self::published_type(key)),
                Box::new(Self::published_type(value)),
            ),
            Type::Tuple(elements) => {
                Type::Tuple(elements.iter().map(Self::published_type).collect())
            }
            Type::Proc(parameters, result) => Type::Proc(
                parameters.iter().map(Self::published_type).collect(),
                Box::new(Self::published_type(result)),
            ),
            Type::BoundProc {
                receiver,
                parameters,
                result,
            } => Type::BoundProc {
                receiver: Box::new(Self::published_type(receiver)),
                parameters: parameters.iter().map(Self::published_type).collect(),
                result: Box::new(Self::published_type(result)),
            },
            Type::Union(members) => Type::union(members.iter().map(Self::published_type)),
            Type::Intersection(members) => {
                Type::intersection(members.iter().map(Self::published_type))
            }
            other => other.clone(),
        }
    }

    pub(super) fn strictness_at(&self, offset: usize) -> Strictness {
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

    pub(super) fn reports_missing_api<'node>(&self, node: &Node<'node>) -> bool {
        let (start, _) = prism::span(node);
        strictness_rank(self.strictness_at(start)) >= strictness_rank(Strictness::True)
            && !self.is_rbi_definition(node)
    }

    pub(super) fn report_missing_method_if_needed<'node>(
        &mut self,
        node: &Node<'node>,
        receiver: &Type,
        name: &str,
        resolved: bool,
    ) {
        let (start, end) = prism::span(node);
        self.report_missing_method_if_needed_at(
            SourceSite::new(start, end),
            receiver,
            name,
            resolved,
        );
    }

    pub(super) fn report_missing_method_if_needed_at(
        &mut self,
        site: SourceSite,
        receiver: &Type,
        name: &str,
        resolved: bool,
    ) {
        let resolved = resolved || self.receiver_handles_missing_method(receiver, name);
        self.report_missing_method_message_if_needed_at(
            site,
            receiver,
            resolved,
            format!(
                "Method `{name}` does not exist on `{}`",
                sorbet_receiver_description(receiver)
            ),
        );
    }

    pub(super) fn known_respond_to_guard(
        &self,
        receiver: Option<&Node<'_>>,
        method: &str,
        environment: &Environment,
    ) -> bool {
        let Some(receiver) = receiver else {
            return false;
        };
        if let Some(local) = receiver.as_local_variable_read_node() {
            return environment.known_respond_to(
                &format!("\u{1}local:{}", prism::constant_name(local.name())),
                method,
            );
        }
        if let Some(instance_variable) = receiver.as_instance_variable_read_node() {
            return environment.known_respond_to(
                &format!(
                    "\u{1}ivar:{}",
                    prism::constant_name(instance_variable.name())
                ),
                method,
            );
        }
        false
    }

    pub(super) fn report_missing_method_component_if_needed_at(
        &mut self,
        site: SourceSite,
        receiver: &Type,
        name: &str,
        union: &Type,
    ) {
        if !self.reports_missing_api_at(site)
            || receiver.is_any()
            || receiver.contains_any()
            || receiver.is_never()
            || self.receiver_handles_missing_method(receiver, name)
        {
            return;
        }
        self.error_at(
            site,
            format!("Method `{name}` does not exist on `{receiver}` component of `{union}`"),
        );
    }

    fn report_missing_method_message_if_needed_at(
        &mut self,
        site: SourceSite,
        receiver: &Type,
        resolved: bool,
        message: String,
    ) {
        if resolved
            || !self.reports_missing_api_at(site)
            || receiver.is_any()
            || receiver.contains_any()
            || receiver.is_never()
        {
            return;
        }
        self.error_at(site, message);
    }

    pub(super) fn constant_is_known(&self, environment: &Environment, name: &str) -> bool {
        let name = name.trim_start_matches("::");
        if name == "T" || name.starts_with("T::") {
            return true;
        }
        if name == "ARGV" {
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
            || self.constant_is_known_through_ancestors(&resolved)
    }

    pub(super) fn report_missing_constant_if_needed<'node>(
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

    pub(super) fn is_rbi_definition(&self, node: &Node<'_>) -> bool {
        let (start, end) = prism::span(node);
        range_containing(&self.rbi_ranges, start).is_some_and(|(_, range_end)| end <= range_end)
    }

    pub(super) fn is_rbi_offset(&self, offset: usize) -> bool {
        range_containing(&self.rbi_ranges, offset).is_some()
    }

    pub(super) fn record<'node>(&mut self, node: &Node<'node>, type_: Type) -> Type {
        let (start, end) = prism::span(node);
        let untyped_origin = if type_.contains_any() {
            self.reporting
                .untyped_origins
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
            self.reporting.report && Self::is_send_node(node),
            untyped_origin,
        )
    }

    pub(super) fn deduplicate_types(types: Vec<InferredType>) -> Vec<InferredType> {
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

    pub(super) fn error<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.reporting.report || self.reporting.suppress_diagnostics {
            return;
        }
        let (start, end) = prism::span(node);
        self.error_at(SourceSite::new(start, end), message);
    }

    pub(super) fn note<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.reporting.report || self.reporting.suppress_diagnostics {
            return;
        }
        let (start, end) = prism::span(node);
        self.note_at(SourceSite::new(start, end), message);
    }

    pub(super) fn error_at_or_node(
        &mut self,
        node: Option<&Node<'_>>,
        site: SourceSite,
        message: String,
    ) {
        if let Some(node) = node {
            self.error(node, message);
        } else {
            self.error_at(site, message);
        }
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

    pub(super) fn reports_missing_api_at(&self, site: SourceSite) -> bool {
        strictness_rank(self.strictness_at(site.start)) >= strictness_rank(Strictness::True)
            && !self
                .rbi_ranges
                .iter()
                .any(|(start, end)| site.start >= *start && site.end <= *end)
    }

    pub(super) fn record_at(
        &mut self,
        site: SourceSite,
        type_: Type,
        is_send: bool,
        untyped_origin: Option<UntypedOrigin>,
    ) -> Type {
        // Seed and fixpoint passes only need the type as an evaluator result.
        // Per-expression products are consumed after the final reporting pass;
        // publishing them during every intermediate pass needlessly walks
        // nested types and allocates a transient entry for every operation.
        if !self.reporting.report {
            return type_;
        }
        let untyped_origin = if type_.contains_any() {
            self.reporting
                .untyped_origins
                .get(&(site.start, site.end))
                .copied()
                .or(untyped_origin)
                .or(Some(UntypedOrigin::Propagated))
        } else {
            None
        };
        let published_type = Self::published_type(&type_);
        let report = self.reporting.report;
        self.reporting.types.push(InferredType {
            start: site.start,
            end: site.end,
            type_: published_type,
            untyped_origin,
            is_send: report && is_send,
        });
        type_
    }

    pub(super) fn remember_untyped_origin_at(
        &mut self,
        site: SourceSite,
        type_: &Type,
        origin: UntypedOrigin,
    ) {
        if type_.contains_any() {
            self.reporting
                .untyped_origins
                .insert((site.start, site.end), origin);
        }
    }

    pub(super) fn error_at(&mut self, site: SourceSite, message: impl Into<String>) {
        if !self.reporting.report || self.reporting.suppress_diagnostics {
            return;
        }
        self.reporting
            .diagnostics
            .push(Diagnostic::error_with_line_map(
                self.program.source,
                &self.program.line_map,
                message,
                site.start,
                site.end,
            ));
    }

    pub(super) fn error_at_allow_duplicate(
        &mut self,
        site: SourceSite,
        message: impl Into<String>,
    ) {
        if !self.reporting.report || self.reporting.suppress_diagnostics {
            return;
        }
        let message = message.into();
        self.reporting
            .preserve_duplicate_diagnostics
            .entry((site.start, site.end, message.clone()))
            .or_insert(2);
        self.reporting
            .diagnostics
            .push(Diagnostic::error_with_line_map(
                self.program.source,
                &self.program.line_map,
                message,
                site.start,
                site.end,
            ));
    }

    pub(super) fn note_at(&mut self, site: SourceSite, message: impl Into<String>) {
        if !self.reporting.report || self.reporting.suppress_diagnostics {
            return;
        }
        self.reporting
            .diagnostics
            .push(Diagnostic::note_with_line_map(
                self.program.source,
                &self.program.line_map,
                message,
                site.start,
                site.end,
            ));
    }
}

fn sorbet_receiver_description(receiver: &Type) -> String {
    match receiver {
        Type::Named(name, arguments) if name == "Class" && arguments.len() == 1 => {
            format!("T.class_of({})", arguments[0])
        }
        _ => receiver.to_string(),
    }
}
