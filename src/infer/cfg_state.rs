use super::{Environment, Flow, FlowKind, MethodKey, Strictness};
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
    pub(super) environment: Environment,
    pub(super) flow: Flow,
    /// The exception currently being routed through an unwind edge. A
    /// rescue handler consumes this fact on its matching branch; an
    /// unmatched branch keeps it until the next handler or outer unwind.
    pub(super) pending_exception: Option<Type>,
}

impl BlockState {
    pub(super) fn with_values(
        environment: Environment,
        values: Vec<Option<Type>>,
        flow: Flow,
    ) -> Self {
        Self {
            values,
            environment,
            flow,
            pending_exception: None,
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
        let pending_exception = match (&self.pending_exception, &other.pending_exception) {
            (Some(left), Some(right)) => Some(left.join(right)),
            (Some(exception), None) | (None, Some(exception)) => Some(exception.clone()),
            (None, None) => None,
        };
        Self {
            values,
            environment,
            flow: self.flow.union(other.flow),
            pending_exception,
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

    pub(super) fn route_exception(&mut self, exception: Type) {
        self.pending_exception = Some(exception);
        self.flow = Flow::abrupt(FlowKind::Raise);
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
}
