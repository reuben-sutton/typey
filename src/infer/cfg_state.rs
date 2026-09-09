use super::hash_shape::HashShape;
use super::{Environment, Flow, FlowKind, MethodKey, OutcomeTypes, Strictness};
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
    pub(super) values: Vec<Option<Type>>,
    pub(super) hash_shapes: Vec<Option<HashShape>>,
    pub(super) environment: Environment,
    pub(super) flow: Flow,
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
            values,
            hash_shapes: Vec::new(),
            environment,
            flow,
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
            values,
            hash_shapes,
            environment,
            flow: self.flow.union(other.flow),
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
    }

    pub(super) fn set_pending_outcome(&mut self, kind: FlowKind, type_: Type) {
        self.pending_outcomes = OutcomeTypes::default();
        self.pending_outcomes.set(kind, type_);
    }

    pub(super) fn handle_exception(&mut self) {
        self.pending_exception = None;
        self.flow = self.flow.without(FlowKind::Raise);
        if self.flow.is_empty() {
            self.flow = Flow::normal();
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BodyContext {
    pub(super) body: hir::BodyId,
    pub(super) method: Option<MethodKey>,
    pub(super) self_type: Type,
    pub(super) parameters: hir::Parameters,
    pub(super) strictness: Strictness,
    pub(super) closure_kind: Option<hir::ClosureKind>,
}
