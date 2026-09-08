use super::{Analyzer, SourceSite};

mod assignment;
mod body;
mod builtins;
mod calls;
mod collections;
mod construction;
mod exceptions;
mod flow;
mod globals;
mod patterns;
mod preflight;
mod value;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CfgFallbackKind {
    UnsupportedOperation,
    UnsupportedEdge,
    // Retained as an explicit telemetry bucket while the migration is
    // complete. The owned CFG path must not use it; a future parser bridge
    // must be visible in the report instead of becoming an unclassified gap.
    #[allow(dead_code)]
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
    pub(super) fn record_cfg_fallback_at(
        &mut self,
        site: SourceSite,
        kind: &str,
        fallback: CfgFallbackKind,
    ) {
        self.record_cfg_fallback_detail_at(site, kind, fallback, None);
    }

    pub(super) fn record_cfg_fallback_detail_at(
        &mut self,
        site: SourceSite,
        kind: &str,
        fallback: CfgFallbackKind,
        detail: Option<&str>,
    ) {
        self.cfg_transfer_fallbacks.record(fallback);
        if self.config.debug {
            if let Some(detail) = detail {
                eprintln!(
                    "[typey] CFG fallback for {kind} at {:?}: {detail}",
                    (site.start, site.end)
                );
            } else {
                eprintln!(
                    "[typey] CFG fallback for {kind} at {:?}: no owned transfer is available",
                    (site.start, site.end)
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::cfg_state::BlockState;
    use super::super::{Environment, Flow, FlowKind};
    use crate::types::Type;

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
