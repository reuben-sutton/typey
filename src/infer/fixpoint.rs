use super::{MethodKey, SharedKey};
use crate::types::Type;
use std::collections::{BTreeMap, BTreeSet};

/// Mutable state for the method-summary fixpoint.
///
/// The worklist and its dependency edges have one lifecycle: seed, evaluate
/// rounds until summaries stabilize, then run the final reporting pass. Keeping
/// them together prevents the evaluator from having to understand how a
/// changed summary is scheduled.
pub(super) struct FixpointState {
    pub(super) active_methods: BTreeSet<MethodKey>,
    pub(super) changed_methods: BTreeSet<MethodKey>,
    pub(super) pending_returns: BTreeMap<MethodKey, (Type, bool)>,
    pub(super) collecting_returns: bool,
    pub(super) method_callers: BTreeMap<MethodKey, BTreeSet<MethodKey>>,
    pub(super) method_shared_reads: BTreeMap<MethodKey, BTreeSet<SharedKey>>,
    pub(super) shared_readers: BTreeMap<SharedKey, BTreeSet<MethodKey>>,
    pub(super) symbol_method_returns: BTreeMap<MethodKey, String>,
    pub(super) changed_shared: BTreeSet<SharedKey>,
    pub(super) debug_phase: &'static str,
    pub(super) debug_round: usize,
    pub(super) debug_nodes: usize,
}

impl Default for FixpointState {
    fn default() -> Self {
        Self {
            active_methods: BTreeSet::new(),
            changed_methods: BTreeSet::new(),
            pending_returns: BTreeMap::new(),
            collecting_returns: false,
            method_callers: BTreeMap::new(),
            method_shared_reads: BTreeMap::new(),
            shared_readers: BTreeMap::new(),
            symbol_method_returns: BTreeMap::new(),
            changed_shared: BTreeSet::new(),
            debug_phase: "idle",
            debug_round: 0,
            debug_nodes: 0,
        }
    }
}
