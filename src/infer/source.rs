//! Source locations used by inference paths that no longer need parser nodes.

use super::{strictness_rank, Analyzer, Environment, InferredType, Strictness, UntypedOrigin};
use crate::diagnostic::Diagnostic;
use crate::hir;
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::BTreeMap;

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
#[derive(Debug)]
pub(super) struct ReportingState {
    pub(super) report: bool,
    pub(super) suppress_diagnostics: bool,
    pub(super) diagnostics: Vec<Diagnostic>,
    pub(super) types: Vec<InferredType>,
    pub(super) untyped_origins: BTreeMap<(usize, usize), UntypedOrigin>,
}

impl ReportingState {
    pub(super) fn new(diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            report: true,
            suppress_diagnostics: false,
            diagnostics,
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

    pub(super) fn constant_is_known(&self, environment: &Environment, name: &str) -> bool {
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
        self.rbi_ranges
            .iter()
            .any(|(range_start, range_end)| start >= *range_start && end <= *range_end)
    }

    pub(super) fn is_rbi_offset(&self, offset: usize) -> bool {
        self.rbi_ranges
            .iter()
            .any(|(range_start, range_end)| offset >= *range_start && offset < *range_end)
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
        self.reporting.types.push(InferredType {
            start: site.start,
            end: site.end,
            type_: type_.clone(),
            untyped_origin,
            is_send: self.reporting.report && is_send,
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
