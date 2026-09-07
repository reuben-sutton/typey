use crate::types::Type;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FlowKind {
    Normal,
    Return,
    Raise,
    Break,
    Next,
    Retry,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Flow(u8);

impl Flow {
    const NORMAL: u8 = 1;

    fn bit(kind: FlowKind) -> u8 {
        match kind {
            FlowKind::Normal => Self::NORMAL,
            FlowKind::Return => 1 << 1,
            FlowKind::Raise => 1 << 2,
            FlowKind::Break => 1 << 3,
            FlowKind::Next => 1 << 4,
            FlowKind::Retry => 1 << 5,
        }
    }

    pub(super) fn normal() -> Self {
        Self(Self::NORMAL)
    }

    pub(super) fn empty() -> Self {
        Self(0)
    }

    pub(super) fn abrupt(kind: FlowKind) -> Self {
        debug_assert_ne!(kind, FlowKind::Normal);
        Self(Self::bit(kind))
    }

    pub(super) fn contains(self, kind: FlowKind) -> bool {
        self.0 & Self::bit(kind) != 0
    }

    pub(super) fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    pub(super) fn without(self, kind: FlowKind) -> Self {
        Self(self.0 & !Self::bit(kind))
    }

    pub(super) fn is_terminated(self) -> bool {
        !self.contains(FlowKind::Normal)
    }

    pub(super) fn is_empty(self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct OutcomeTypes {
    pub(super) return_type: Type,
    pub(super) raise_type: Type,
    pub(super) break_type: Type,
    pub(super) next_type: Type,
    pub(super) retry_type: Type,
}

impl Default for OutcomeTypes {
    fn default() -> Self {
        Self {
            return_type: Type::Never,
            raise_type: Type::Never,
            break_type: Type::Never,
            next_type: Type::Never,
            retry_type: Type::Never,
        }
    }
}

impl OutcomeTypes {
    pub(super) fn for_kind(kind: FlowKind, type_: Type) -> Self {
        let mut result = Self::default();
        result.set(kind, type_);
        result
    }

    pub(super) fn set(&mut self, kind: FlowKind, type_: Type) {
        match kind {
            FlowKind::Normal => {}
            FlowKind::Return => self.return_type = type_,
            FlowKind::Raise => self.raise_type = type_,
            FlowKind::Break => self.break_type = type_,
            FlowKind::Next => self.next_type = type_,
            FlowKind::Retry => self.retry_type = type_,
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        Self {
            return_type: Self::join_type(&self.return_type, &other.return_type),
            raise_type: Self::join_type(&self.raise_type, &other.raise_type),
            break_type: Self::join_type(&self.break_type, &other.break_type),
            next_type: Self::join_type(&self.next_type, &other.next_type),
            retry_type: Self::join_type(&self.retry_type, &other.retry_type),
        }
    }

    fn join_type(left: &Type, right: &Type) -> Type {
        if left.is_never() {
            right.clone()
        } else if right.is_never() {
            left.clone()
        } else {
            left.join(right)
        }
    }

    pub(super) fn without(&self, kind: FlowKind) -> Self {
        let mut result = self.clone();
        result.set(kind, Type::Never);
        result
    }

    pub(super) fn all(&self) -> Type {
        Type::union([
            self.return_type.clone(),
            self.raise_type.clone(),
            self.break_type.clone(),
            self.next_type.clone(),
            self.retry_type.clone(),
        ])
    }

    pub(super) fn flow(&self) -> Flow {
        let mut flow = Flow::empty();
        for (kind, type_) in [
            (FlowKind::Return, &self.return_type),
            (FlowKind::Raise, &self.raise_type),
            (FlowKind::Break, &self.break_type),
            (FlowKind::Next, &self.next_type),
            (FlowKind::Retry, &self.retry_type),
        ] {
            if !type_.is_never() {
                flow = flow.union(Flow::abrupt(kind));
            }
        }
        flow
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Eval {
    /// The join of values produced by every possible outcome.
    pub(super) type_: Type,
    /// Possible control-flow outcomes of this expression.
    pub(super) flow: Flow,
    /// Value and environment continuation are present only for normal flow.
    pub(super) normal_type: Option<Type>,
    /// Per-outcome values for abrupt control flow.
    pub(super) abrupt: OutcomeTypes,
}

impl Eval {
    pub(super) fn value(type_: Type) -> Self {
        Self {
            type_: type_.clone(),
            flow: Flow::normal(),
            normal_type: Some(type_),
            abrupt: OutcomeTypes::default(),
        }
    }

    pub(super) fn returned(type_: Type) -> Self {
        Self::abrupt(FlowKind::Return, type_)
    }

    pub(super) fn raised(type_: Type) -> Self {
        Self::abrupt(FlowKind::Raise, type_)
    }

    pub(super) fn broken(type_: Type) -> Self {
        Self::abrupt(FlowKind::Break, type_)
    }

    pub(super) fn continued(type_: Type) -> Self {
        Self::abrupt(FlowKind::Next, type_)
    }

    pub(super) fn unreachable() -> Self {
        Self::from_parts(None, OutcomeTypes::default(), Flow::empty())
    }

    pub(super) fn retried(type_: Type) -> Self {
        Self::abrupt(FlowKind::Retry, type_)
    }

    pub(super) fn abrupt(kind: FlowKind, type_: Type) -> Self {
        Self {
            type_: type_.clone(),
            flow: Flow::abrupt(kind),
            normal_type: None,
            abrupt: OutcomeTypes::for_kind(kind, type_),
        }
    }

    pub(super) fn from_parts(normal_type: Option<Type>, abrupt: OutcomeTypes, flow: Flow) -> Self {
        let abrupt_type = abrupt.all();
        let type_ = normal_type
            .as_ref()
            .map_or_else(|| abrupt_type.clone(), |normal| normal.join(&abrupt_type));
        Self {
            type_,
            flow,
            normal_type,
            abrupt,
        }
    }

    pub(super) fn combine(left: &Self, right: &Self) -> Self {
        let normal_type = match (&left.normal_type, &right.normal_type) {
            (Some(left), Some(right)) => Some(left.join(right)),
            (Some(type_), None) | (None, Some(type_)) => Some(type_.clone()),
            (None, None) => None,
        };
        Self::from_parts(
            normal_type,
            left.abrupt.join(&right.abrupt),
            left.flow.union(right.flow),
        )
    }

    pub(super) fn method_return_type(&self) -> Type {
        match (&self.normal_type, self.abrupt.return_type.is_never()) {
            (Some(normal), true) => normal.clone(),
            (Some(normal), false) => normal.join(&self.abrupt.return_type),
            (None, false) => self.abrupt.return_type.clone(),
            (None, true) => Type::Never,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combining_evaluations_preserves_normal_and_abrupt_outcomes() {
        let normal = Eval::value(Type::Integer);
        let returned = Eval::returned(Type::String);

        let combined = Eval::combine(&normal, &returned);

        assert_eq!(combined.normal_type, Some(Type::Integer));
        assert_eq!(combined.abrupt.return_type, Type::String);
        assert_eq!(combined.type_, Type::union([Type::Integer, Type::String]));
        assert!(combined.flow.contains(FlowKind::Normal));
        assert!(combined.flow.contains(FlowKind::Return));
    }

    #[test]
    fn outcome_types_derive_abrupt_flow_from_non_never_values() {
        let mut outcomes = OutcomeTypes::default();
        outcomes.set(FlowKind::Raise, Type::named("RuntimeError"));
        outcomes.set(FlowKind::Next, Type::Symbol);

        let flow = outcomes.flow();

        assert!(flow.contains(FlowKind::Raise));
        assert!(flow.contains(FlowKind::Next));
        assert!(!flow.contains(FlowKind::Return));
    }
}
