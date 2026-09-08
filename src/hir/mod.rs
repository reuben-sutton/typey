//! Typey's owned semantic high-level intermediate representation.
//!
//! HIR values deliberately contain no Prism nodes and no inference state. A
//! lowered program owns its vectors and uses integer IDs to refer to other
//! values. Source locations are represented by [`Span`] rather than by a
//! parser-backed location, so a program can outlive the Prism parse tree.

use std::fmt;

pub mod lower;

pub use lower::lower;

/// The source file containing a span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

macro_rules! id_type {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u32);
    };
}

id_type!(BodyId);
id_type!(ClosureId);
id_type!(DeclId);
id_type!(ExprId);
id_type!(LocalId);
id_type!(ScopeId);

/// A file-relative byte span in the source program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    #[must_use]
    pub const fn new(file: FileId, start: u32, end: u32) -> Self {
        Self { file, start, end }
    }

    #[must_use]
    pub const fn len(self) -> u32 {
        self.end.saturating_sub(self.start)
    }
}

/// An owned Ruby identifier.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(String);

impl Name {
    #[must_use]
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<String> for Name {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A constant path kept as source text after lowering.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstantPath(String);

impl ConstantPath {
    #[must_use]
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<String> for ConstantPath {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl From<&str> for ConstantPath {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl fmt::Display for ConstantPath {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A lowered body and the expression that produces its result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub owner: BodyOwner,
    pub parameters: Parameters,
    pub root: ExprId,
    pub span: Span,
}

/// The lexical owner of a body. This records syntax, not runtime block
/// binding; inference decides the eventual value of `self` for a closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyOwner {
    TopLevel,
    Method { name: Name, singleton: bool },
    Class(ConstantPath),
    Module(ConstantPath),
    SingletonClass,
    Closure(ClosureId),
}

/// Ruby parameter kinds retained by the HIR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParameterKind {
    Required,
    Optional,
    Rest,
    Post,
    RequiredKeyword,
    OptionalKeyword,
    KeywordRest,
    Block,
    Forwarded,
    Anonymous,
}

/// One owned parameter declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parameter {
    pub local: Option<LocalId>,
    pub name: Option<Name>,
    pub kind: ParameterKind,
    pub span: Span,
}

/// The parameter list for a body or closure.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Parameters {
    pub parameters: Vec<Parameter>,
    pub forwarding: bool,
    pub span: Option<Span>,
}

/// A closure whose body and parameters are owned by the lowered program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closure {
    pub body: BodyId,
    pub parameters: Parameters,
    pub span: Span,
    pub lexical_scope: ScopeId,
    pub kind: ClosureKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClosureKind {
    Block,
    Lambda,
}

/// Literal values represented without a dependency on the type system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    Nil,
    True,
    False,
    Integer(String),
    Float(String),
    Rational(String),
    Imaginary(String),
    String(String),
    Symbol(String),
    RegularExpression(String),
    XString(String),
}

/// Reads of values that are not method calls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Read {
    Local(LocalId),
    InstanceVariable(Name),
    ClassVariable(Name),
    Global(Name),
    Constant(ConstantPath),
    SelfValue,
    Numbered(u32),
    It,
    BackReference(Name),
}

/// An expression in the owned program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

/// The initial value-producing HIR vocabulary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Nil,
    Literal(Literal),
    Read(Read),
    Assign {
        target: AssignTarget,
        /// The source span of the assignment target, excluding the operator
        /// and assigned value.
        target_span: Span,
        value: ExprId,
        operator: AssignOperator,
    },
    Call(Call),
    Array(Vec<ArrayElement>),
    Hash(Vec<HashElement>),
    Closure(ClosureId),
    Sequence(Vec<ExprId>),
    If {
        condition: ExprId,
        then_body: ExprId,
        else_body: Option<ExprId>,
    },
    Case(CaseExpr),
    Loop(LoopExpr),
    Begin(BeginExpr),
    Return(Option<ExprId>),
    Break(Option<ExprId>),
    Next(Option<ExprId>),
    Retry,
    Definition(DeclId),
    Unsupported(Unsupported),
}

/// A call preserves syntax-level argument shape until inference evaluates it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Call {
    pub receiver: Receiver,
    pub name: Name,
    pub arguments: Vec<Argument>,
    /// Exclusive ends of the flattened [`arguments`] vector for each
    /// top-level Ruby argument. Keyword hashes lower into several semantic
    /// arguments but remain one source-level group.
    pub argument_groups: Vec<usize>,
    /// Source spans of the top-level Ruby arguments, aligned with
    /// [`argument_groups`].
    pub argument_spans: Vec<Span>,
    pub block: Option<BlockArgument>,
    pub safe_navigation: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Receiver {
    Implicit,
    Explicit(ExprId),
    Super,
    Yield,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Argument {
    Positional(ExprId),
    Splat(ExprId),
    Keyword {
        name: Name,
        name_span: Span,
        value: ExprId,
    },
    KeywordSplat(ExprId),
    Forwarded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockArgument {
    Inline(ClosureId),
    Passed(ExprId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayElement {
    Value(ExprId),
    Splat { value: ExprId, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HashElement {
    Pair { key: ExprId, value: ExprId },
    Splat { value: ExprId, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignTarget {
    Local(LocalId),
    InstanceVariable(Name),
    ClassVariable(Name),
    Global(Name),
    Constant(ConstantPath),
    Attribute {
        receiver: ExprId,
        name: Name,
    },
    Index {
        receiver: ExprId,
        arguments: Vec<Argument>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignOperator {
    Set,
    And,
    Or,
    Binary(Name),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseExpr {
    pub scrutinee: Option<ExprId>,
    pub arms: Vec<CaseArm>,
    pub else_body: Option<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseArm {
    pub conditions: Vec<ExprId>,
    pub body: ExprId,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopKind {
    While,
    Until,
    For,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopExpr {
    pub kind: LoopKind,
    pub condition: ExprId,
    /// The source span of the loop predicate, including syntax such as
    /// parentheses that may be transparent in the value-producing HIR.
    pub condition_span: Span,
    pub body: Option<ExprId>,
    /// The assignment target for `for`; absent for `while` and `until`.
    pub index: Option<AssignTarget>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BeginExpr {
    pub body: Option<ExprId>,
    pub rescue: Vec<RescueClause>,
    pub else_body: Option<ExprId>,
    pub ensure: Option<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RescueClause {
    pub exceptions: Vec<ExprId>,
    pub reference: Option<LocalId>,
    pub body: Option<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unsupported {
    pub kind: Name,
    /// Executable HIR expressions discovered inside this unsupported parent.
    /// The parent remains an explicit handoff, but nested calls and writes do
    /// not become orphaned outside the body graph.
    pub children: Vec<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub span: Span,
    pub kind: DeclarationKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclarationKind {
    Method {
        name: Name,
        singleton: bool,
        body: BodyId,
    },
    Class {
        name: ConstantPath,
        body: Option<BodyId>,
    },
    Module {
        name: ConstantPath,
        body: Option<BodyId>,
    },
    SingletonClass {
        body: Option<BodyId>,
    },
}

/// An owned lowered Ruby program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub file: Option<FileId>,
    pub root: Option<BodyId>,
    pub expressions: Vec<Expr>,
    pub bodies: Vec<Body>,
    pub closures: Vec<Closure>,
    pub declarations: Vec<Declaration>,
    /// Names for [`LocalId`] values allocated while lowering this program.
    /// Local IDs remain the semantic references used by HIR; the table is
    /// only the owned spelling needed by later phases.
    pub locals: Vec<Name>,
}

impl Program {
    #[must_use]
    pub fn expression(&self, id: ExprId) -> Option<&Expr> {
        self.expressions.get(id.0 as usize)
    }

    #[must_use]
    pub fn body(&self, id: BodyId) -> Option<&Body> {
        self.bodies.get(id.0 as usize)
    }

    #[must_use]
    pub fn closure(&self, id: ClosureId) -> Option<&Closure> {
        self.closures.get(id.0 as usize)
    }

    #[must_use]
    pub fn declaration(&self, id: DeclId) -> Option<&Declaration> {
        self.declarations.get(id.0 as usize)
    }

    #[must_use]
    pub fn local_name(&self, id: LocalId) -> Option<&Name> {
        self.locals.get(id.0 as usize)
    }
}
