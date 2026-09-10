//! Analysis lifecycle and fixpoint orchestration.

use super::*;

impl<'src> Analyzer<'src> {
    pub(super) fn record_inferred_return(
        &mut self,
        key: MethodKey,
        actual: Type,
        terminates: bool,
    ) {
        match self.fixpoint.pending_returns.entry(key) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert((actual, terminates));
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                let (current, current_terminates) = entry.get_mut();
                *current = current.join(&actual);
                *current_terminates &= terminates;
            }
        }
    }

    pub(super) fn record_inferred_raise(&mut self, key: MethodKey, actual: Type) {
        if actual.is_never() {
            return;
        }
        match self.fixpoint.pending_raises.entry(key) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(actual);
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                let current = entry.get().clone();
                entry.insert(current.join(&actual));
            }
        }
    }

    pub(super) fn commit_inferred_returns(&mut self) {
        let pending_returns = std::mem::take(&mut self.fixpoint.pending_returns);
        for (key, (return_type, return_terminates)) in pending_returns {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                if !state.explicit {
                    let changed = state.return_type.as_ref() != Some(&return_type)
                        || state.return_terminates != return_terminates;
                    state.return_type = Some(return_type);
                    state.return_terminates = return_terminates;
                    if changed {
                        self.fixpoint.changed_methods.insert(key);
                    }
                }
            }
        }
        let pending_raises = std::mem::take(&mut self.fixpoint.pending_raises);
        for (key, raise_type) in pending_raises {
            if let Some(state) = self.declarations.methods.get_mut(&key) {
                let next = state
                    .raise_type
                    .as_ref()
                    .map_or_else(|| raise_type.clone(), |current| current.join(&raise_type));
                let changed = state.raise_type.as_ref() != Some(&next);
                state.raise_type = Some(next);
                if changed {
                    self.fixpoint.changed_methods.insert(key);
                }
            }
        }
    }

    pub(super) fn run<'node>(mut self, root: &Node<'node>) -> CheckResult {
        let run_started = std::time::Instant::now();
        if self.config.debug {
            eprintln!("[typey] registering declarations");
        }
        self.register_methods(root);
        let parse_diagnostics = std::mem::take(&mut self.reporting.diagnostics);
        if self.config.debug {
            eprintln!(
                "[typey] registered {} methods, {} classes, and {} type aliases",
                self.declarations.methods.len(),
                self.declarations.classes.len(),
                self.declarations.type_aliases.len()
            );
            eprintln!(
                "[typey] compiled {} HIR bodies into CFG ({} source, {} RBI)",
                self.program
                    .cfg_index
                    .as_ref()
                    .map_or(0, cfg::CfgIndex::body_count),
                self.program.cfg_index.as_ref().map_or(0, |index| {
                    index.body_count() - index.body_count_in_ranges(&self.rbi_ranges)
                }),
                self.program
                    .cfg_index
                    .as_ref()
                    .map_or(0, |index| index.body_count_in_ranges(&self.rbi_ranges))
            );
            eprintln!(
                "[typey] CFG unsupported handoffs: {}",
                self.program
                    .cfg_index
                    .as_ref()
                    .map_or(0, cfg::CfgIndex::unsupported_count)
            );
            eprintln!(
                "[typey] registration complete in {:?}",
                run_started.elapsed()
            );
        }

        // First solve summaries without emitting diagnostics or retaining
        // transient node types. This is the same shape as Spinel's analysis:
        // all definitions are registered, then the tables are refined until
        // one complete pass makes no change.
        self.reporting.report = false;
        self.seed_calls = true;
        self.filter_method_bodies = false;
        self.fixpoint.debug_phase = "seed";
        self.fixpoint.debug_round = 0;
        self.reporting.types.clear();
        self.fixpoint.debug_nodes = 0;
        if self.config.debug {
            eprintln!("[typey] seeding top-level call sites");
        }
        self.fixpoint.pending_returns.clear();
        self.fixpoint.pending_raises.clear();
        self.fixpoint.collecting_returns = true;
        let seed_started = std::time::Instant::now();
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);
        self.fixpoint.collecting_returns = false;
        self.commit_inferred_returns();
        if self.config.debug {
            eprintln!("[typey] seed complete in {:?}", seed_started.elapsed());
        }
        self.seed_calls = false;
        self.fixpoint.changed_methods.clear();
        self.fixpoint.changed_shared.clear();

        let mut pending_methods = self
            .declarations
            .methods
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut round = 0;
        // The worklist is driven solely by actual summary changes. There is
        // no arbitrary round limit: once no method or shared value changes,
        // the pending set is empty and the analysis has reached its fixed
        // point.
        loop {
            if pending_methods.is_empty() {
                break;
            }

            round += 1;
            self.fixpoint.active_methods = pending_methods.clone();
            self.filter_method_bodies = true;
            self.fixpoint.changed_methods.clear();
            self.fixpoint.changed_shared.clear();
            self.fixpoint.debug_phase = "inference";
            self.fixpoint.debug_round = round;
            self.reporting.types.clear();
            self.fixpoint.debug_nodes = 0;
            if self.config.debug {
                eprintln!(
                    "[typey] worklist round {round}: evaluating {} scheduled methods",
                    pending_methods.len()
                );
            }
            let round_started = std::time::Instant::now();
            // Return summaries are computed synchronously: every method body
            // reads the summaries committed by the previous round, and all
            // candidates from this round are committed together below. This
            // avoids source-order effects when a caller appears before its
            // callee or when conditional branches define the same method.
            self.fixpoint.pending_returns.clear();
            self.fixpoint.pending_raises.clear();
            self.fixpoint.collecting_returns = true;
            let mut environment = Environment::default();
            self.eval_node(root, &mut environment);
            self.fixpoint.collecting_returns = false;
            self.commit_inferred_returns();

            let changed_methods = std::mem::take(&mut self.fixpoint.changed_methods);
            let changed_shared = std::mem::take(&mut self.fixpoint.changed_shared);
            let mut next_pending = BTreeSet::new();
            for method in &changed_methods {
                next_pending.insert(method.clone());
                if let Some(callers) = self.fixpoint.method_callers.get(method) {
                    next_pending.extend(callers.iter().cloned());
                }
            }
            for shared_key in &changed_shared {
                if let Some(readers) = self.fixpoint.shared_readers.get(shared_key) {
                    next_pending.extend(readers.iter().cloned());
                }
            }
            if self.config.debug {
                eprintln!(
                    "[typey] worklist round {round} complete: {} changed methods, {} changed shared keys, {} scheduled next",
                    changed_methods.len(),
                    changed_shared.len(),
                    next_pending.len(),
                );
                eprintln!(
                    "[typey] worklist round {round} elapsed {:?}",
                    round_started.elapsed()
                );
            }
            pending_methods = next_pending;
        }

        // Re-run once with settled summaries. This final pass is the only pass
        // that publishes diagnostics and per-node types to callers.
        self.reporting.report = true;
        self.reporting.diagnostics = parse_diagnostics;
        self.seed_calls = false;
        self.reporting.types.clear();
        self.filter_method_bodies = false;
        self.fixpoint.active_methods.clear();
        self.fixpoint.debug_phase = "final";
        self.fixpoint.debug_round = 0;
        self.fixpoint.debug_nodes = 0;
        if self.config.debug {
            eprintln!("[typey] final reporting pass");
        }
        let final_started = std::time::Instant::now();
        let mut environment = Environment::default();
        self.eval_node(root, &mut environment);
        if self.config.debug {
            eprintln!(
                "[typey] final pass complete in {:?}",
                final_started.elapsed()
            );
        }

        self.report_inference_gaps();
        let types = Self::deduplicate_types(std::mem::take(&mut self.reporting.types));
        let mut seen_diagnostics = BTreeSet::new();
        self.reporting.diagnostics.retain(|diagnostic| {
            seen_diagnostics.insert((
                matches!(diagnostic.severity, Severity::Note),
                diagnostic.start,
                diagnostic.end,
                diagnostic.message.clone(),
            ))
        });
        self.reporting.diagnostics.sort_by(|left, right| {
            left.start
                .cmp(&right.start)
                .then_with(|| left.message.cmp(&right.message))
        });
        if self.config.debug {
            eprintln!(
                "[typey] CFG transfers: {} bodies ({} source, {} RBI), {} calls, {} assignments, {} values, {} fallbacks (unsupported operations {}, unsupported edges {}, legacy bridges {})",
                self.cfg_transfer_bodies,
                self.cfg_transfer_bodies - self.cfg_transfer_rbi_bodies,
                self.cfg_transfer_rbi_bodies,
                self.cfg_transfer_calls,
                self.cfg_transfer_assignments,
                self.cfg_transfer_values,
                self.cfg_transfer_fallbacks.total(),
                self.cfg_transfer_fallbacks.unsupported_operation,
                self.cfg_transfer_fallbacks.unsupported_edge,
                self.cfg_transfer_fallbacks.legacy_bridge
            );
            eprintln!(
                "[typey] complete: {} diagnostics, {} recorded types in {:?}",
                self.reporting.diagnostics.len(),
                types.len(),
                run_started.elapsed()
            );
        }
        CheckResult {
            diagnostics: self.reporting.diagnostics,
            types,
        }
    }

    fn report_inference_gaps(&mut self) {
        if self.config.strictness == Strictness::Ignore && self.strictness_ranges.is_empty() {
            return;
        }

        let gaps = self
            .declarations
            .definitions
            .iter()
            .filter_map(|(offset, key)| {
                let strictness = self.strictness_at(*offset);
                if strictness_rank(strictness) < strictness_rank(Strictness::Strict) {
                    return None;
                }
                let state = self.declarations.methods.get(key)?;
                if state.explicit {
                    return None;
                }
                let unresolved_parameter = state
                    .params
                    .iter()
                    .any(|type_| type_.as_ref().map_or(true, Type::is_any));
                let unresolved_keyword = state
                    .keywords
                    .values()
                    .any(|type_| type_.as_ref().map_or(true, Type::is_any));
                let unresolved_return = state.return_type.as_ref().map_or(true, Type::is_any);
                (unresolved_parameter || unresolved_keyword || unresolved_return)
                    .then_some((*offset, key.clone()))
            })
            .collect::<Vec<_>>();

        for (offset, key) in gaps {
            let name = key.owner.as_ref().map_or_else(
                || key.name.clone(),
                |owner| format!("{owner}::{}", key.name),
            );
            self.reporting.diagnostics.push(Diagnostic::error(
                self.program.source,
                format!(
                    "Method `{name}` has insufficient inferred type information for strict mode"
                ),
                offset,
                offset,
            ));
        }
    }
}
