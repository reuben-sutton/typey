//! Analysis lifecycle and fixpoint orchestration.

use super::*;

impl<'src> Analyzer<'src> {
    fn index_owned_method_definitions(&mut self) {
        let definitions = self
            .program
            .hir_program
            .declarations
            .iter()
            .enumerate()
            .filter_map(|(index, declaration)| {
                let hir::DeclarationKind::Method { .. } = declaration.kind else {
                    return None;
                };
                let declaration_id = hir::DeclId(index as u32);
                let key = self
                    .declarations
                    .definitions
                    .get(&(declaration.span.start as usize))
                    .cloned()?;
                (!self.is_rbi_offset(declaration.span.start as usize))
                    .then_some((declaration_id, key))
            })
            .collect::<BTreeMap<_, _>>();
        let root_definitions = definitions
            .iter()
            .filter_map(|(declaration_id, _)| {
                let declaration = self.program.hir_program.declaration(*declaration_id)?;
                let parent = self
                    .program
                    .hir_program
                    .bodies
                    .iter()
                    .filter(|body| {
                        body.span.start <= declaration.span.start
                            && body.span.end >= declaration.span.end
                    })
                    .min_by_key(|body| body.span.len())?;
                matches!(
                    parent.owner,
                    hir::BodyOwner::TopLevel
                        | hir::BodyOwner::Class(_)
                        | hir::BodyOwner::Module(_)
                        | hir::BodyOwner::SingletonClass
                )
                .then_some(*declaration_id)
            })
            .collect();
        self.owned_method_definitions = definitions;
        self.root_method_definitions = root_definitions;

        let namespace_bodies = self
            .program
            .hir_program
            .bodies
            .iter()
            .enumerate()
            .filter_map(|(index, body)| {
                matches!(
                    body.owner,
                    hir::BodyOwner::Class(_)
                        | hir::BodyOwner::Module(_)
                        | hir::BodyOwner::SingletonClass
                )
                .then_some((hir::BodyId(index as u32), body))
            })
            .collect::<Vec<_>>();
        self.namespace_body_parents = namespace_bodies
            .iter()
            .filter_map(|(body_id, body)| {
                namespace_bodies
                    .iter()
                    .filter(|(candidate_id, candidate)| {
                        candidate_id != body_id
                            && candidate.span.start <= body.span.start
                            && candidate.span.end >= body.span.end
                    })
                    .min_by_key(|(_, candidate)| candidate.span.len())
                    .map(|(parent_id, _)| (*body_id, *parent_id))
            })
            .collect();
        self.namespace_body_always_replay = namespace_bodies
            .iter()
            .filter_map(|(body_id, _)| {
                let graph = self
                    .program
                    .cfg_graphs
                    .as_ref()
                    .and_then(|graphs| graphs.get(body_id.0 as usize))?;
                graph
                    .blocks
                    .iter()
                    .flat_map(|block| block.operations.iter())
                    .any(|operation| match &operation.kind {
                        cfg::OperationKind::Call { name, .. } => matches!(
                            name.as_str(),
                            "alias_method"
                                | "class_eval"
                                | "class_exec"
                                | "define_method"
                                | "define_singleton_method"
                                | "eval"
                                | "instance_eval"
                                | "instance_exec"
                                | "module_eval"
                                | "module_exec"
                        ),
                        cfg::OperationKind::Definition { .. } => true,

                        _ => false,
                    })
                    .then_some(*body_id)
            })
            .collect();
    }

    pub(super) fn namespace_dependency_key(body_id: hir::BodyId) -> MethodKey {
        MethodKey {
            owner: None,
            name: format!("<namespace-body:{}>", body_id.0),
            singleton: true,
        }
    }

    pub(super) fn namespace_body_is_active(&self, body_id: hir::BodyId) -> bool {
        self.namespace_body_always_replay.contains(&body_id)
            || self
                .active_namespace_bodies
                .as_ref()
                .is_none_or(|active| active.contains(&body_id))
    }

    fn retain_inactive_namespace_method_definitions(&mut self) {
        let Some(active) = self.active_namespace_bodies.as_ref() else {
            return;
        };
        let retained = self
            .namespace_body_method_definitions
            .iter()
            .filter(|(body_id, _)| {
                !active.contains(body_id) && !self.namespace_body_always_replay.contains(body_id)
            })
            .flat_map(|(_, definitions)| definitions.iter().copied())
            .collect::<BTreeSet<_>>();
        self.reachable_method_definitions.extend(retained);
    }

    fn changed_namespace_bodies(
        &self,
        changed_methods: &BTreeSet<MethodKey>,
        changed_shared: &BTreeSet<SharedKey>,
    ) -> BTreeSet<hir::BodyId> {
        // Namespace bodies can observe shared state through framework hooks
        // and dynamic dispatch without producing a direct read edge. A
        // shared-state change therefore invalidates every namespace body;
        // method-only changes can use the precise call dependency graph below.
        if !changed_shared.is_empty() {
            return self.namespace_body_keys.keys().copied().collect();
        }
        let mut bodies = BTreeSet::new();
        for method in changed_methods {
            if let Some(callers) = self.fixpoint.method_callers.get(method) {
                bodies.extend(
                    callers
                        .iter()
                        .filter_map(|caller| self.namespace_body_key_ids.get(caller).copied()),
                );
            }
        }
        for shared_key in changed_shared {
            if let Some(readers) = self.fixpoint.shared_readers.get(shared_key) {
                bodies.extend(
                    readers
                        .iter()
                        .filter_map(|reader| self.namespace_body_key_ids.get(reader).copied()),
                );
            }
        }

        let mut ancestors = bodies.clone();
        for body_id in bodies {
            let mut current = body_id;
            while let Some(parent) = self.namespace_body_parents.get(&current).copied() {
                if !ancestors.insert(parent) {
                    break;
                }
                current = parent;
            }
        }
        ancestors
    }

    fn eval_scheduled_method_definitions(
        &mut self,
        methods: &BTreeSet<MethodKey>,
    ) -> Result<(), String> {
        let scheduled = self
            .owned_method_definitions
            .iter()
            .filter(|(declaration_id, key)| {
                self.root_method_definitions.contains(declaration_id)
                    && self.reachable_method_definitions.contains(declaration_id)
                    && methods.contains(*key)
            })
            .map(|(declaration_id, _)| *declaration_id)
            .collect::<Vec<_>>();

        for declaration_id in scheduled {
            let Some(declaration) = self
                .program
                .hir_program
                .declaration(declaration_id)
                .cloned()
            else {
                continue;
            };
            let hir::DeclarationKind::Method {
                name,
                singleton,
                body,
            } = declaration.kind
            else {
                continue;
            };
            let mut environment = Environment::default();
            self.eval_owned_method_definition(
                declaration.span,
                name,
                singleton,
                body,
                &mut environment,
            )?;
        }
        Ok(())
    }

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
        self.index_owned_method_definitions();
        let parse_diagnostics = std::mem::take(&mut self.reporting.diagnostics);
        if self.config.debug {
            eprintln!(
                "[typey] registered {} methods, {} classes, and {} type aliases",
                self.declarations.methods.len(),
                self.declarations.classes.len(),
                self.declarations.type_aliases.len()
            );
            eprintln!(
                "[typey] CFG body count: {} executable source HIR bodies ({} signature declaration bodies, {} RBI bodies excluded from application count)",
                self.cfg_application_body_count(),
                self.cfg_signature_body_count(),
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
        self.cfg_transferred_bodies_this_pass.clear();
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
        let mut pending_namespace_bodies = None;
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
            self.active_namespace_bodies = pending_namespace_bodies.take();
            self.fixpoint.debug_phase = "inference";
            self.fixpoint.debug_round = round;
            self.reporting.types.clear();
            self.cfg_transferred_bodies_this_pass.clear();
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
            // Replay the root for top-level and namespace effects, but do not
            // recursively enter ordinary statically rooted method definitions
            // from each class body. Those definitions are evaluated directly
            // below in source order. Dynamic and nested definitions remain in
            // the root pass because their runtime reachability is contextual.
            self.reachable_method_definitions.clear();
            self.retain_inactive_namespace_method_definitions();
            self.collect_method_definitions = true;
            self.skip_root_method_definitions = true;
            let mut environment = Environment::default();
            self.eval_node(root, &mut environment);
            self.collect_method_definitions = false;
            self.skip_root_method_definitions = false;
            self.fixpoint.active_methods = pending_methods.clone();
            if let Err(reason) = self.eval_scheduled_method_definitions(&pending_methods) {
                // A body which cannot be transferred through owned CFG still
                // gets the established root-replay fallback for this round.
                // The owned transfer normally reports the failure before
                // publishing any body result, so this path remains rare.
                if self.config.debug {
                    eprintln!("[typey] direct method worklist fallback: {reason}");
                }
                let previous_active_namespace_bodies = self.active_namespace_bodies.take();
                let previous_collect_method_definitions = self.collect_method_definitions;
                self.collect_method_definitions = true;
                self.skip_root_method_definitions = false;
                let mut fallback_environment = Environment::default();
                self.eval_node(root, &mut fallback_environment);
                self.collect_method_definitions = previous_collect_method_definitions;
                self.active_namespace_bodies = previous_active_namespace_bodies;
            }
            self.fixpoint.collecting_returns = false;
            self.commit_inferred_returns();

            let changed_methods = std::mem::take(&mut self.fixpoint.changed_methods);
            let changed_shared = std::mem::take(&mut self.fixpoint.changed_shared);
            let mut next_pending = BTreeSet::new();
            let mut next_namespace_bodies = BTreeSet::new();
            for method in &changed_methods {
                next_pending.insert(method.clone());
                if let Some(callers) = self.fixpoint.method_callers.get(method) {
                    for caller in callers {
                        if let Some(body_id) = self.namespace_body_key_ids.get(caller) {
                            next_namespace_bodies.insert(*body_id);
                        } else {
                            next_pending.insert(caller.clone());
                        }
                    }
                }
            }
            for shared_key in &changed_shared {
                if let Some(readers) = self.fixpoint.shared_readers.get(shared_key) {
                    for reader in readers {
                        if let Some(body_id) = self.namespace_body_key_ids.get(reader) {
                            next_namespace_bodies.insert(*body_id);
                        } else {
                            next_pending.insert(reader.clone());
                        }
                    }
                }
            }
            next_namespace_bodies
                .extend(self.changed_namespace_bodies(&changed_methods, &changed_shared));
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
            pending_namespace_bodies = Some(next_namespace_bodies);
        }

        // Re-run once with settled summaries. This final pass is the only pass
        // that publishes diagnostics and per-node types to callers.
        self.reporting.report = true;
        self.reporting.diagnostics = parse_diagnostics;
        self.seed_calls = false;
        self.reporting.types.clear();
        self.cfg_transferred_bodies_this_pass.clear();
        self.filter_method_bodies = false;
        self.fixpoint.active_methods.clear();
        self.active_namespace_bodies = None;
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
            let signature_bodies = &self.signature_declaration_bodies;
            let missing_source_bodies = self
                .program
                .hir_program
                .bodies
                .iter()
                .enumerate()
                .filter_map(|(index, body)| {
                    let body_id = hir::BodyId(index as u32);
                    (!signature_bodies.contains(&body_id)
                        && !self.is_rbi_offset(body.span.start as usize)
                        && !self.cfg_transferred_bodies.contains(&body_id))
                    .then_some((body_id, body))
                })
                .collect::<Vec<_>>();
            let signature_source_bodies = self
                .program
                .hir_program
                .bodies
                .iter()
                .enumerate()
                .filter(|(index, body)| {
                    signature_bodies.contains(&hir::BodyId(*index as u32))
                        && !self.is_rbi_body(body)
                })
                .count();
            if signature_source_bodies > 0 {
                eprintln!(
                    "[typey] CFG signature declaration bodies excluded from application coverage: {signature_source_bodies}"
                );
            }
            if !missing_source_bodies.is_empty() {
                eprintln!(
                    "[typey] CFG source bodies not transferred: {}",
                    missing_source_bodies.len()
                );
                for (body_id, body) in missing_source_bodies {
                    let start = body.span.start as usize;
                    let end = body.span.end as usize;
                    let preview_end = end.min(start.saturating_add(120));
                    let preview = self
                        .program
                        .source
                        .get(start..preview_end)
                        .map_or_else(String::new, |source| {
                            String::from_utf8_lossy(source).replace(['\n', '\r', '\t'], " ")
                        });
                    let reason = self
                        .cfg_body_preflight_failure(body_id)
                        .map_or_else(|| "body was not entered".to_owned(), |(_, reason)| reason);
                    eprintln!(
                        "[typey]   {body_id:?} {:?} at {start}..{end} ({reason}): {preview}",
                        body.owner,
                    );
                }
            }
            eprintln!(
                "[typey] CFG transfers: {} body visits, {} unique bodies ({} source, {} RBI), {} calls, {} assignments, {} values, {} fallbacks (unsupported operations {}, unsupported edges {}, legacy bridges {})",
                self.cfg_transfer_bodies,
                self.cfg_transferred_bodies.len(),
                self.cfg_transferred_bodies
                    .iter()
                    .filter(|body_id| {
                        self.program
                            .hir_program
                            .body(**body_id)
                            .is_some_and(|body| {
                                !signature_bodies.contains(body_id)
                                    && !self.is_rbi_offset(body.span.start as usize)
                            })
                    })
                    .count(),
                self.cfg_transferred_bodies
                    .iter()
                    .filter(|body_id| {
                        self.program
                            .hir_program
                            .body(**body_id)
                            .is_some_and(|body| self.is_rbi_offset(body.span.start as usize))
                    })
                    .count(),
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

    fn cfg_signature_body_count(&self) -> usize {
        let Some(_index) = self.program.cfg_index.as_ref() else {
            return 0;
        };
        let signature_bodies = &self.signature_declaration_bodies;
        self.program
            .hir_program
            .bodies
            .iter()
            .enumerate()
            .filter(|(index, body)| {
                signature_bodies.contains(&hir::BodyId(*index as u32)) && !self.is_rbi_body(body)
            })
            .count()
    }

    fn cfg_application_body_count(&self) -> usize {
        let Some(_index) = self.program.cfg_index.as_ref() else {
            return 0;
        };
        let signature_bodies = &self.signature_declaration_bodies;
        self.program
            .hir_program
            .bodies
            .iter()
            .enumerate()
            .filter(|(index, body)| {
                !signature_bodies.contains(&hir::BodyId(*index as u32)) && !self.is_rbi_body(body)
            })
            .count()
    }

    fn is_rbi_body(&self, body: &hir::Body) -> bool {
        self.is_rbi_offset(body.span.start as usize)
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
