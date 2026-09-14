//! The parser-to-owned-program entry boundary.
//!
//! Prism is still used to retain source locations and inline annotation
//! syntax, but it is no longer an execution engine. Every executable body is
//! lowered once to HIR and transferred through its cached CFG. This module is
//! deliberately small because parser-shaped recursive evaluation was the
//! source of the old second implementation of Ruby semantics.

use super::*;
use ruby_prism::Node;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_node<'node>(
        &mut self,
        node: &Node<'node>,
        environment: &mut Environment,
    ) -> Eval {
        if !self.defer_inline_assertions {
            if let Some(assertion) = self.inline_assertion_for_node(node) {
                if assertion.kind == AssertionKind::SelfAs {
                    let previous_self_type = environment.self_type.clone();
                    environment.self_type = self.resolve_type_names(
                        &assertion.type_,
                        self.lexical_owner(environment).as_deref(),
                    );
                    let result = self.eval_owned_entry(node, environment);
                    environment.self_type = previous_self_type;
                    return result;
                }
            }
        }
        self.eval_owned_entry(node, environment)
    }

    fn eval_owned_entry<'node>(
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

        let span = prism::span(node);
        if let Some(declaration_id) = self.program.hir_declaration_ids.get(&span).copied() {
            return match self.eval_owned_definition(declaration_id, None, environment) {
                Ok(type_) => Eval::value(self.record(node, type_)),
                Err(reason) => {
                    if self.config.debug {
                        eprintln!(
                            "[typey] owned declaration transfer stopped at {:?}: {reason}",
                            span
                        );
                    }
                    self.cfg_unsupported_result(node, "declaration")
                }
            };
        }

        if let Some(body_id) = self.program.hir_body_ids.get(&span).copied() {
            return match self.eval_cfg_body_owned(
                self.owned_body_site(body_id),
                body_id,
                environment,
                true,
            ) {
                Ok(result) => result,
                Err(reason) => {
                    if self.config.debug {
                        eprintln!(
                            "[typey] owned body transfer stopped at {:?}: {reason}",
                            span
                        );
                    }
                    self.cfg_unsupported_result(node, "body")
                }
            };
        }

        // This is only a safety boundary for parser-facing helper APIs which
        // have not yet been retired. Ordinary application expressions should
        // always arrive through a CFG operation, where their HIR identity and
        // source span are already available.
        self.cfg_unsupported_result(node, "parser expression")
    }
}
