//! Typey's owned, syntax-only control-flow graph.
//!
//! CFG values deliberately contain no inferred types, environments, or
//! diagnostics.  A graph is built from owned HIR and can therefore be reused
//! by each fixpoint inference pass without reparsing or rediscovering control
//! flow.

use crate::hir::{self, BodyId, ClosureId, ConstantPath, ExprId, LocalId, Name, Span};

pub mod index;
pub mod lower;
pub mod transfer;

pub use index::CfgIndex;
pub use lower::{build, build_all};

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
    /// Conditional regions retain the owned HIR expression IDs that created
    /// their branch and join blocks.  The IDs let the transfer phase execute
    /// a branch without rediscovering it from parser nodes.
    pub conditionals: Vec<Conditional>,
    /// Entry blocks for ensure regions. The transfer phase uses this owned
    /// marker to distinguish an ensure completion from an ordinary jump.
    pub ensure_entries: Vec<BlockId>,
    /// Rescue handler regions whose normal exits are separate from the
    /// protected body. The transfer phase can inspect these handlers even
    /// when no statically known call in the protected body raises.
    pub rescue_regions: Vec<RescueRegion>,
    /// Source spans where lowering required a transitional unsupported handoff.
    pub unsupported_spans: Vec<Span>,
    /// Expressions that occur after an unconditional outcome in a sequence.
    /// They are retained for source diagnostics even though no executable CFG
    /// path reaches them.
    pub unreachable_expressions: Vec<ExprId>,
    /// The value produced by each HIR expression, when it has a normally
    /// completing path. This keeps the graph connected to source HIR without
    /// embedding parser or inference state in the CFG.
    pub expression_values: Vec<Option<ValueId>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RescueRegion {
    pub entry: BlockId,
    pub exit: BlockId,
    pub protected_entry: BlockId,
    /// Whether the protected expression contains a send that can provide a
    /// runtime exception path. Handler analysis still runs without this, but
    /// a handler value is only part of the enclosing expression when such a
    /// path exists.
    pub may_raise: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conditional {
    pub expression: ExprId,
    pub condition: ExprId,
    pub then_body: ExprId,
    pub else_body: Option<ExprId>,
    pub truthy: BlockId,
    pub falsy: BlockId,
    pub join: BlockId,
    /// Loop conditions retain Ruby's conservative nil result for a truthy
    /// first iteration, even when ordinary branch narrowing can prove the
    /// condition itself truthy.
    pub loop_condition: bool,
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
            .or_else(|| {
                self.blocks
                    .iter()
                    .flat_map(|block| block.operations.iter())
                    .find_map(|operation| {
                        (operation.expression == Some(expression))
                            .then_some(operation.result)
                            .flatten()
                    })
            })
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
    /// Logical-assignment RHS operations defer source inline assertions until
    /// the assignment result is written, matching Ruby's expression scope.
    pub defer_inline_assertion: bool,
    /// Operations which probe the operand of `defined?` retain sends and
    /// inferred values but must not publish ordinary operand diagnostics.
    pub suppress_diagnostics: bool,
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
        logical: bool,
    },
    MultiWrite {
        value: ValueId,
        lefts: Vec<hir::AssignTarget>,
        rest: Option<hir::AssignTarget>,
        rights: Vec<hir::AssignTarget>,
    },
    /// Extract one logical value from a multiple-assignment RHS before
    /// sending it to a dynamic attribute or index target.
    MultiWriteElement {
        value: ValueId,
        part: MultiWritePart,
    },
    Defined {
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
        preserve_fixed_shape: bool,
    },
    BuildHash {
        elements: Vec<HashOperand>,
    },
    BuildInterpolated {
        kind: hir::InterpolatedKind,
    },
    BuildRange {
        left: Option<ValueId>,
        right: Option<ValueId>,
        exclude_end: bool,
    },
    /// A method declaration evaluates to `nil`. The declaration itself is
    /// already registered in the workspace; class/module declaration bodies
    /// remain outside this transitional operation until their runtime owner
    /// effects have an owned transfer contract.
    Definition {
        declaration: hir::DeclId,
        value: Option<ValueId>,
    },
    /// Record a joined expression value without introducing another runtime
    /// operation. This is used for begin/conditional join expressions whose
    /// value is carried by a block parameter.
    Record {
        value: Option<ValueId>,
    },
    /// Publish a joined expression value after applying its source-level
    /// inline assertion. This is distinct from `Record` because ordinary
    /// control-flow joins such as logical assignments must not reapply an
    /// assertion that belongs to one of their child writes.
    ApplyAssertion {
        value: ValueId,
    },
    /// Route a non-local control value through an active ensure region.
    SetOutcome {
        kind: OutcomeKind,
        value: ValueId,
    },
    PatternTest {
        value: ValueId,
        pattern: Pattern,
    },
    /// Bind one iteration element to an owned `for` target before the loop
    /// body executes.
    BindForTarget {
        collection: ValueId,
        target: hir::AssignTarget,
    },
    /// Transitional handoff for HIR variants that do not have a CFG lowering
    /// yet. It has a source span and an explicit result, but no concrete
    /// interpretation.
    Unsupported {
        kind: Name,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MultiWritePart {
    Left(usize),
    Rest,
    Right {
        index: usize,
        left_count: usize,
        right_count: usize,
    },
}

/// A control outcome that must run enclosing ensure bodies before it can
/// terminate or continue to an outer control region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutcomeKind {
    Return,
    Break,
    Next,
    Retry,
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
    Splat { value: ValueId, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HashOperand {
    Pair { key: ValueId, value: ValueId },
    Splat { value: ValueId, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Truthy,
    /// Truthiness test used by a logical assignment. These retain the same
    /// narrowing as [`Pattern::Truthy`] but preserve which side-effecting
    /// assignment protocol is being transferred.
    LogicalAnd,
    LogicalOr,
    Nil,
    /// A collection iteration has both a zero-iteration and a body path,
    /// even when the collection's Ruby truthiness is known.
    Iteration,
    Case {
        condition: ValueId,
        expression: ExprId,
        source_place: Option<Place>,
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
    /// An explicit Ruby `return` from a block, which exits the defining
    /// method rather than completing the block normally.
    NonLocalReturn(Option<ValueId>),
    Raise(ValueId),
    /// Complete an ensure body. Normal state continues to `target`; a
    /// pending raised outcome is routed through the block's unwind edge.
    EnsureComplete {
        expression: ExprId,
        target: BlockId,
        arguments: Vec<ValueId>,
        /// The enclosing ensure entry for a pending non-local outcome.
        pending_target: Option<BlockId>,
    },
    Unreachable,
}
