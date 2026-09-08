//! Source locations used by inference paths that no longer need parser nodes.

use super::{strictness_rank, Analyzer, InferredType, Strictness, UntypedOrigin};
use crate::diagnostic::Diagnostic;
use crate::hir;
use crate::types::Type;

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

    pub(super) const fn from_span(span: hir::Span, expression: Option<hir::ExprId>) -> Self {
        Self {
            start: span.start as usize,
            end: span.end as usize,
            expression,
        }
    }
}

impl<'src> Analyzer<'src> {
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
