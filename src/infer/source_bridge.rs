//! Parser-facing source-location helpers.
//!
//! CFG is the sole semantic evaluator. This module only keeps the public
//! parser boundary supplied with source locations while older helper APIs are
//! retired.

use super::*;
use ruby_prism::Node;

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_unsupported_result(&self, node: &Node<'_>, kind: &str) -> Eval {
        if self.config.debug {
            eprintln!(
                "[typey] unsupported owned {kind} at {:?}: continuing with T.anything",
                prism::span(node)
            );
        }
        Eval::value(Type::Anything)
    }

    pub(super) fn owned_body_site(&self, body: hir::BodyId) -> SourceSite {
        let span = self
            .program
            .hir_program
            .body(body)
            .and_then(|body| self.program.hir_program.expression(body.root))
            .map_or_else(
                || {
                    self.program
                        .hir_program
                        .body(body)
                        .map_or(hir::Span::new(hir::FileId(0), 0, 0), |body| body.span)
                },
                |expression| expression.span,
            );
        SourceSite::from_span(span, None)
    }
}
