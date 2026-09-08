//! Typey's owned, syntax-only control-flow graph.
//!
//! CFG values deliberately contain no inferred types, environments, or
//! diagnostics.  A graph is built from owned HIR and can therefore be reused
//! by each fixpoint inference pass without reparsing or rediscovering control
//! flow.

use crate::hir::{self, BodyId, ClosureId, ConstantPath, ExprId, LocalId, Name, Span};

pub mod lower;

pub use lower::build;

macro_rules! id_type {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u32);
    };
}

id_type!(BlockId);
id_type!(ValueId);

/// A body-local value-flow graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cfg {
    pub body: BodyId,
    pub entry: BlockId,
    pub blocks: Vec<BasicBlock>,
    /// Source spans where lowering required a transitional unsupported handoff.
    pub unsupported_spans: Vec<Span>,
    /// The value produced by each HIR expression, when it has a normally
    /// completing path. This keeps the graph connected to source HIR without
    /// embedding parser or inference state in the CFG.
    pub expression_values: Vec<Option<ValueId>>,
}

impl Cfg {
    #[must_use]
    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.get(id.0 as usize)
    }

    #[must_use]
    pub fn value_for(&self, expression: ExprId) -> Option<ValueId> {
        self.expression_values
            .get(expression.0 as usize)
            .copied()
            .flatten()
    }
}

/// A basic block with explicit operations and one control-flow terminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlock {
    pub id: BlockId,
    pub parameters: Vec<BlockParameter>,
    pub operations: Vec<Operation>,
    pub terminator: Terminator,
    /// The active exception successor for operations in this block.
    pub unwind: Option<BlockId>,
}

/// A value arriving from predecessors of a block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockParameter {
    pub value: ValueId,
    pub incoming: Vec<(BlockId, ValueId)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operation {
    pub span: Span,
    /// The HIR expression whose evaluation produced this operation, when the
    /// operation corresponds to a source expression rather than a synthetic
    /// join/seed operation.
    pub expression: Option<ExprId>,
    pub result: Option<ValueId>,
    pub kind: OperationKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationKind {
    Const {
        value: hir::Literal,
    },
    Read {
        place: Place,
    },
    /// Reads which do not correspond to a storage place, such as `self` or a
    /// numbered reference. They remain explicit rather than becoming an
    /// invented `Place`.
    ReadSpecial {
        read: hir::Read,
    },
    Write {
        place: Place,
        value: ValueId,
    },
    Call {
        receiver: ReceiverOperand,
        name: Name,
        arguments: Vec<ArgumentOperand>,
        block: Option<BlockOperand>,
        safe_navigation: bool,
    },
    MakeClosure {
        closure: ClosureId,
    },
    BuildArray {
        elements: Vec<ArrayOperand>,
    },
    BuildHash {
        elements: Vec<HashOperand>,
    },
    PatternTest {
        value: ValueId,
        pattern: Pattern,
    },
    /// Transitional handoff for HIR variants that do not have a CFG lowering
    /// yet. It has a source span and an explicit result, but no concrete
    /// interpretation.
    Unsupported {
        kind: Name,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    Local(LocalId),
    InstanceVariable(Name),
    ClassVariable(Name),
    Global(Name),
    Constant(ConstantPath),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiverOperand {
    Implicit,
    Value(ValueId),
    Super,
    Yield,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgumentOperand {
    Positional(ValueId),
    Splat(ValueId),
    Keyword { name: Name, value: ValueId },
    KeywordSplat(ValueId),
    Forwarded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockOperand {
    Inline(ClosureId),
    Passed(ValueId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayOperand {
    Value(ValueId),
    Splat(ValueId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HashOperand {
    Pair { key: ValueId, value: ValueId },
    Splat(ValueId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Truthy,
    Nil,
    Case {
        condition: ValueId,
        expression: ExprId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    Jump {
        target: BlockId,
        arguments: Vec<ValueId>,
    },
    Branch {
        condition: ValueId,
        truthy: BlockId,
        falsy: BlockId,
    },
    Return(Option<ValueId>),
    Raise(ValueId),
    Unreachable,
}
