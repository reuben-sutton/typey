use super::cfg_state::BlockState;
use super::{Analyzer, Environment, Eval, Flow, FlowKind, HirCallView, OutcomeTypes, SourceSite};
use crate::cfg;
use crate::hir;
use crate::prism;
use crate::types::Type;
use ruby_prism::Node;

mod assignment;
mod body;
mod legacy;
mod patterns;
mod preflight;
mod value;

fn cfg_global_refinement_key(name: &str) -> String {
    format!("\u{1}cfg-global:{name}")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CfgFallbackKind {
    UnsupportedOperation,
    UnsupportedEdge,
    LegacyBridge,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct CfgFallbackCounters {
    pub(super) unsupported_operation: usize,
    pub(super) unsupported_edge: usize,
    pub(super) legacy_bridge: usize,
}

impl CfgFallbackCounters {
    pub(super) fn record(&mut self, kind: CfgFallbackKind) {
        let counter = match kind {
            CfgFallbackKind::UnsupportedOperation => &mut self.unsupported_operation,
            CfgFallbackKind::UnsupportedEdge => &mut self.unsupported_edge,
            CfgFallbackKind::LegacyBridge => &mut self.legacy_bridge,
        };
        *counter = counter.saturating_add(1);
    }

    pub(super) fn total(&self) -> usize {
        self.unsupported_operation
            .saturating_add(self.unsupported_edge)
            .saturating_add(self.legacy_bridge)
    }
}

impl<'src> Analyzer<'src> {
    pub(super) fn has_cfg_call_operation(&self, node: &Node<'_>) -> bool {
        self.cfg_index
            .as_ref()
            .is_some_and(|index| index.has_call(prism::span(node)))
    }

    pub(super) fn has_cfg_assignment_operation(&self, node: &Node<'_>) -> bool {
        let span = prism::span(node);
        self.cfg_index
            .as_ref()
            .is_some_and(|index| index.has_call(span) || index.has_write(span))
    }

    pub(super) fn record_cfg_fallback(
        &mut self,
        node: &Node<'_>,
        kind: &str,
        fallback: CfgFallbackKind,
    ) {
        self.record_cfg_fallback_at(
            SourceSite::from_prism_span(prism::span(node)),
            kind,
            fallback,
        );
    }

    pub(super) fn record_cfg_fallback_at(
        &mut self,
        site: SourceSite,
        kind: &str,
        fallback: CfgFallbackKind,
    ) {
        self.cfg_transfer_fallbacks.record(fallback);
        if self.config.debug {
            eprintln!(
                "[typey] CFG fallback for {kind} at {:?}: no owned transfer is available",
                (site.start, site.end)
            );
        }
    }

    pub(super) fn transfer_cfg_call<'node>(
        &mut self,
        node: &Node<'node>,
        call: HirCallView<'node>,
        environment: &mut Environment,
    ) -> Eval {
        self.cfg_transfer_calls = self.cfg_transfer_calls.saturating_add(1);
        self.record_cfg_fallback(node, "call", CfgFallbackKind::LegacyBridge);
        // The CFG supplies the dispatch name and argument-shape operation.
        // HirCallView retains only Prism child nodes so the existing transfer
        // machinery can evaluate child expressions until the owned value
        // evaluator lands.
        self.eval_call_result(node, &call, environment)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment(name: &str, type_: Type) -> Environment {
        let mut environment = Environment::default();
        environment.bind(name, type_);
        environment
    }

    #[test]
    fn normal_path_wins_over_an_abrupt_path() {
        let normal = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let returned = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::abrupt(FlowKind::Return),
        );

        let joined = normal.join(&returned);

        assert_eq!(joined.environment.get("value"), Type::String);
        assert_eq!(joined.values, vec![Some(Type::String.join(&Type::Integer))]);
        assert!(joined.flow.contains(FlowKind::Normal));
        assert!(joined.flow.contains(FlowKind::Return));
    }

    #[test]
    fn two_normal_paths_join_values_and_environment_facts() {
        let left = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::normal(),
        );

        let joined = left.join(&right);

        let expected = Type::String.join(&Type::Integer);
        assert_eq!(joined.environment.get("value"), expected);
        assert_eq!(joined.values, vec![Some(expected)]);
    }

    #[test]
    fn missing_value_on_one_edge_is_not_invented_at_the_join() {
        let left = BlockState::with_values(
            Environment::default(),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(Environment::default(), vec![None], Flow::normal());

        assert_eq!(left.join(&right).values, vec![None]);
    }
}
