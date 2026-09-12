use super::hash_shape::HashShape;
use super::{CowState, Environment, Flow, FlowKind, MethodKey, OutcomeTypes, Strictness};
use crate::cfg;
use crate::hir;
use crate::types::Type;

/// The inference-side state at a CFG block boundary.
///
/// CFG construction remains type-free. This state is the first boundary where
/// value IDs, environments, and abrupt flow outcomes become abstract facts
/// that can be joined by the generic CFG worklist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BlockState {
    pub(super) values: CowState<Vec<Option<Type>>>,
    pub(super) hash_shapes: CowState<Vec<Option<HashShape>>>,
    pub(super) environment: Environment,
    pub(super) flow: Flow,
    /// Whether at least one normal path reaches this state.  An exceptional
    /// path through an `ensure` executes the cleanup body as ordinary code,
    /// so its `flow` also contains `Normal`; keep this bit separate to avoid
    /// mistaking that cleanup-only path for a normal continuation afterward.
    pub(super) normal_reachable: bool,
    /// The exception currently being routed through an unwind edge. A
    /// rescue handler consumes this fact on its matching branch; an
    /// unmatched branch keeps it until the next handler or outer unwind.
    pub(super) pending_exception: Option<Type>,
    /// Non-local outcomes are carried through ensure bodies while the CFG
    /// remains on its normal edge. The ensure terminator consumes or routes
    /// these outcomes after the body has executed.
    pub(super) pending_outcomes: OutcomeTypes,
}

impl BlockState {
    pub(super) fn with_values(
        environment: Environment,
        values: Vec<Option<Type>>,
        flow: Flow,
    ) -> Self {
        Self {
            values: CowState::new(values),
            hash_shapes: CowState::new(Vec::new()),
            environment,
            flow,
            normal_reachable: flow.contains(FlowKind::Normal),
            pending_exception: None,
            pending_outcomes: OutcomeTypes::default(),
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        let environment = match (
            self.flow.contains(FlowKind::Normal),
            other.flow.contains(FlowKind::Normal),
        ) {
            (true, false) => self.environment.clone(),
            (false, true) => other.environment.clone(),
            _ => self.environment.join(&other.environment),
        };
        let values = (0..self.values.len().max(other.values.len()))
            .map(
                |index| match (self.values.get(index), other.values.get(index)) {
                    (Some(Some(left)), Some(Some(right))) => Some(left.join(right)),
                    _ => None,
                },
            )
            .collect();
        let hash_shapes = (0..self.hash_shapes.len().max(other.hash_shapes.len()))
            .map(
                |index| match (self.hash_shapes.get(index), other.hash_shapes.get(index)) {
                    (Some(Some(left)), Some(Some(right))) => Some(left.join(right)),
                    _ => None,
                },
            )
            .collect();
        let pending_exception = match (&self.pending_exception, &other.pending_exception) {
            (Some(left), Some(right)) => Some(left.join(right)),
            (Some(exception), None) | (None, Some(exception)) => Some(exception.clone()),
            (None, None) => None,
        };
        let pending_outcomes = self.pending_outcomes.join(&other.pending_outcomes);
        Self {
            values: CowState::new(values),
            hash_shapes: CowState::new(hash_shapes),
            environment,
            flow: self.flow.union(other.flow),
            normal_reachable: self.normal_reachable || other.normal_reachable,
            pending_exception,
            pending_outcomes,
        }
    }

    pub(super) fn value(&self, id: cfg::ValueId) -> Option<Type> {
        self.values.get(id.0 as usize).cloned().flatten()
    }

    pub(super) fn set_value(&mut self, id: cfg::ValueId, type_: Type) {
        let index = id.0 as usize;
        if self.values.len() <= index {
            self.values.resize(index + 1, None);
        }
        self.values[index] = Some(type_);
    }

    pub(super) fn hash_shape(&self, id: cfg::ValueId) -> Option<HashShape> {
        self.hash_shapes.get(id.0 as usize).cloned().flatten()
    }

    pub(super) fn set_hash_shape(&mut self, id: cfg::ValueId, shape: Option<HashShape>) {
        let index = id.0 as usize;
        if self.hash_shapes.len() <= index {
            self.hash_shapes.resize(index + 1, None);
        }
        self.hash_shapes[index] = shape;
    }

    pub(super) fn route_exception(&mut self, exception: Type) {
        self.pending_exception = Some(exception);
        self.pending_outcomes = OutcomeTypes::default();
        self.flow = Flow::abrupt(FlowKind::Raise);
        self.normal_reachable = false;
    }

    pub(super) fn set_pending_outcome(&mut self, kind: FlowKind, type_: Type) {
        self.pending_outcomes = OutcomeTypes::default();
        self.pending_outcomes.set(kind, type_);
    }

    pub(super) fn handle_exception(&mut self) {
        self.pending_exception = None;
        self.flow = self.flow.without(FlowKind::Raise);
        self.normal_reachable = true;
        if self.flow.is_empty() {
            self.flow = Flow::normal();
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BodyContext {
    pub(super) body: hir::BodyId,
    pub(super) top_level: bool,
    pub(super) method: Option<MethodKey>,
    pub(super) self_type: Type,
    pub(super) strictness: Strictness,
    pub(super) closure_kind: Option<hir::ClosureKind>,
}
