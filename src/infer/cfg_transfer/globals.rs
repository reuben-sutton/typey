//! CFG-local tracking for global-variable refinements.

use super::super::{Analyzer, Environment};
use crate::cfg;
use crate::types::Type;

pub(super) fn cfg_global_refinement_key(name: &str) -> String {
    format!("\u{1}cfg-global:{name}")
}

pub(super) fn seed_cfg_global_state(
    analyzer: &Analyzer<'_>,
    graph: &cfg::Cfg,
    environment: &mut Environment,
) {
    for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
        let place = match &operation.kind {
            cfg::OperationKind::Read { place } | cfg::OperationKind::Write { place, .. } => place,
            _ => continue,
        };
        let cfg::Place::Global(name) = place else {
            continue;
        };
        let name = name.as_str();
        if !environment.contains(&cfg_global_refinement_key(name)) {
            let type_ = analyzer.globals.get(name).cloned().unwrap_or(Type::Any);
            environment.bind(cfg_global_refinement_key(name), type_);
        }
    }
}

pub(super) fn commit_cfg_global_state(
    analyzer: &mut Analyzer<'_>,
    graph: &cfg::Cfg,
    environment: &Environment,
) {
    for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
        let place = match &operation.kind {
            cfg::OperationKind::Write { place, .. } => place,
            _ => continue,
        };
        let cfg::Place::Global(name) = place else {
            continue;
        };
        let name = name.as_str();
        if let Some(type_) = environment
            .contains(&cfg_global_refinement_key(name))
            .then(|| environment.get(&cfg_global_refinement_key(name)))
        {
            analyzer.observe_global(name.to_owned(), &type_);
        }
    }
}

pub(super) fn clear_cfg_global_state(graph: &cfg::Cfg, environment: &mut Environment) {
    for operation in graph.blocks.iter().flat_map(|block| &block.operations) {
        let place = match &operation.kind {
            cfg::OperationKind::Read { place } | cfg::OperationKind::Write { place, .. } => place,
            _ => continue,
        };
        let cfg::Place::Global(name) = place else {
            continue;
        };
        environment.remove(&cfg_global_refinement_key(name.as_str()));
    }
}
