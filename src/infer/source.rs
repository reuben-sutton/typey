//! Source locations used by inference paths that no longer need parser nodes.

use super::{strictness_rank, Analyzer, InferredType, Strictness, UntypedOrigin};
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
    pub(super) fn record<'node>(&mut self, node: &Node<'node>, type_: Type) -> Type {
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
        if !self.report || self.suppress_diagnostics {
            return;
        }
        let (start, end) = prism::span(node);
        self.error_at(SourceSite::new(start, end), message);
    }

    pub(super) fn note<'node>(&mut self, node: &Node<'node>, message: impl Into<String>) {
        if !self.report || self.suppress_diagnostics {
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
            self.untyped_origins
                .get(&(site.start, site.end))
                .copied()
                .or(untyped_origin)
                .or(Some(UntypedOrigin::Propagated))
        } else {
            None
        };
        self.types.push(InferredType {
            start: site.start,
            end: site.end,
            type_: type_.clone(),
            untyped_origin,
            is_send: self.report && is_send,
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
            self.untyped_origins.insert((site.start, site.end), origin);
        }
    }

    pub(super) fn error_at(&mut self, site: SourceSite, message: impl Into<String>) {
        if !self.report || self.suppress_diagnostics {
            return;
        }
        self.diagnostics.push(Diagnostic::error_with_line_map(
            self.source,
            &self.line_map,
            message,
            site.start,
            site.end,
        ));
    }

    pub(super) fn note_at(&mut self, site: SourceSite, message: impl Into<String>) {
        if !self.report || self.suppress_diagnostics {
            return;
        }
        self.diagnostics.push(Diagnostic::note_with_line_map(
            self.source,
            &self.line_map,
            message,
            site.start,
            site.end,
        ));
    }
}
