use std::fmt;

/// The small, structural type algebra used by the first Typey checker.
///
/// Types are deliberately values instead of global symbols.  That keeps the
/// inference engine easy to experiment with: a new type constructor can be
/// added here without threading it through a global-state interner first.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    /// Sorbet's gradual escape hatch.
    Any,
    /// The uninhabited type, used for unreachable expressions.
    Never,
    Nil,
    True,
    False,
    Integer,
    Float,
    String,
    Symbol,
    Object,
    /// A nominal Ruby class or module, optionally with type arguments.
    Named(String, Vec<Type>),
    /// An array whose element type is inferred from all writes and literals.
    Array(Box<Type>),
    /// A hash with inferred key and value types.
    Hash(Box<Type>, Box<Type>),
    /// A callable type.  This is intentionally compact until block typing is
    /// expanded to model keyword and rest parameters.
    Proc(Vec<Type>, Box<Type>),
    /// A finite union (least upper bound) of alternatives.
    Union(Vec<Type>),
    /// RBS/Sorbet intersection types. The constructor canonicalizes redundant
    /// components and collapses definitely disjoint primitive intersections.
    Intersection(Vec<Type>),
    /// A named generic parameter that has not been solved yet.
    TypeVar(String),
}

impl Type {
    /// The gradual lattice's dynamic/top element.
    #[must_use]
    pub const fn top() -> Self {
        Self::Any
    }

    /// The lattice's bottom element.
    #[must_use]
    pub const fn bottom() -> Self {
        Self::Never
    }

    #[must_use]
    pub fn named(name: impl Into<String>) -> Self {
        Self::Named(name.into(), Vec::new())
    }

    #[must_use]
    pub fn bool() -> Self {
        Self::union([Self::True, Self::False])
    }

    #[must_use]
    pub fn union<I>(types: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut members: Vec<Self> = Vec::new();
        let mut pending = types.into_iter().collect::<Vec<_>>();
        while let Some(ty) = pending.pop() {
            match ty {
                Self::Any => return Self::Any,
                Self::Never => {}
                Self::Union(inner) => pending.extend(inner),
                other => {
                    // Merge structurally compatible containers before using
                    // the gradual subtype relation. `Any` is both a
                    // consistent subtype and supertype, so relying on
                    // `is_subtype_of` alone would make
                    // `Array(Integer) ∪ Array(Any)` depend on operand order.
                    let mut merged = other;
                    let mut index = 0;
                    while index < members.len() {
                        let Some(joined) = Self::structural_join(&members[index], &merged) else {
                            index += 1;
                            continue;
                        };
                        merged = joined;
                        members.remove(index);
                        index = 0;
                    }
                    // A union is canonical: once a wider member is present,
                    // narrower alternatives are redundant. This is what
                    // makes `join(Integer, Numeric)` equal to `Numeric`.
                    if members.iter().any(|member| merged.is_subtype_of(member)) {
                        continue;
                    }
                    members.retain(|member| !member.is_subtype_of(&merged));
                    members.push(merged);
                }
            }
        }

        match members.len() {
            0 => Self::Never,
            1 => members.pop().expect("one member exists"),
            _ => {
                // Stable output matters for Sorbet-style fixture tests.
                members.sort_by_key(ToString::to_string);
                Self::Union(members)
            }
        }
    }

    fn structural_join(left: &Self, right: &Self) -> Option<Self> {
        match (left, right) {
            (Self::Array(left), Self::Array(right)) => {
                Some(Self::Array(Box::new(left.join(right))))
            }
            (Self::Hash(left_key, left_value), Self::Hash(right_key, right_value)) => {
                Some(Self::Hash(
                    Box::new(left_key.join(right_key)),
                    Box::new(left_value.join(right_value)),
                ))
            }
            (Self::Proc(left_params, left_return), Self::Proc(right_params, right_return))
                if left_params.len() == right_params.len() =>
            {
                Some(Self::Proc(
                    left_params
                        .iter()
                        .zip(right_params)
                        .map(|(left, right)| left.join(right))
                        .collect(),
                    Box::new(left_return.join(right_return)),
                ))
            }
            (Self::Named(left_name, left_args), Self::Named(right_name, right_args))
                if left_name == right_name
                    && (left_args.is_empty()
                        || right_args.is_empty()
                        || left_args.len() == right_args.len()) =>
            {
                if left_args.is_empty() || right_args.is_empty() {
                    Some(Self::Named(left_name.clone(), Vec::new()))
                } else {
                    Some(Self::Named(
                        left_name.clone(),
                        left_args
                            .iter()
                            .zip(right_args)
                            .map(|(left, right)| left.join(right))
                            .collect(),
                    ))
                }
            }
            _ => None,
        }
    }

    /// Least upper bound of two types.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self::union([self.clone(), other.clone()])
    }

    /// Greatest lower bound of two types.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        if self.is_never() || other.is_never() {
            return Self::Never;
        }
        if self.is_any() {
            return other.clone();
        }
        if other.is_any() || self == other {
            return self.clone();
        }

        if let Self::Union(members) = self {
            return Self::union(members.iter().map(|member| member.meet(other)));
        }
        if let Self::Union(members) = other {
            return Self::union(members.iter().map(|member| self.meet(member)));
        }
        if self.is_subtype_of(other) {
            return self.clone();
        }
        if other.is_subtype_of(self) {
            return other.clone();
        }

        if self.is_definitely_disjoint_from(other) {
            return Self::Never;
        }

        match (self, other) {
            (Self::Array(left), Self::Array(right)) => Self::Array(Box::new(left.meet(right))),
            (Self::Hash(left_key, left_value), Self::Hash(right_key, right_value)) => Self::Hash(
                Box::new(left_key.meet(right_key)),
                Box::new(left_value.meet(right_value)),
            ),
            (Self::Proc(left_params, left_return), Self::Proc(right_params, right_return))
                if left_params.len() == right_params.len() =>
            {
                Self::Proc(
                    left_params
                        .iter()
                        .zip(right_params)
                        .map(|(left, right)| left.join(right))
                        .collect(),
                    Box::new(left_return.meet(right_return)),
                )
            }
            (Self::Intersection(left), Self::Intersection(right)) => {
                Self::intersection(left.iter().chain(right).cloned())
            }
            (Self::Intersection(members), other) | (other, Self::Intersection(members)) => {
                Self::intersection(
                    members
                        .iter()
                        .cloned()
                        .chain(std::iter::once(other.clone())),
                )
            }
            _ => Self::intersection([self.clone(), other.clone()]),
        }
    }

    #[must_use]
    pub fn intersection<I>(types: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut members: Vec<Self> = Vec::new();
        let mut pending = types.into_iter().collect::<Vec<_>>();
        while let Some(ty) = pending.pop() {
            match ty {
                Self::Never => return Self::Never,
                Self::Any => {}
                Self::Intersection(inner) => pending.extend(inner),
                other => {
                    if members
                        .iter()
                        .any(|member| member.is_definitely_disjoint_from(&other))
                    {
                        return Self::Never;
                    }
                    // A narrower component subsumes a wider component in an
                    // intersection: `meet(Integer, Numeric)` is Integer.
                    if members.iter().any(|member| member.is_subtype_of(&other)) {
                        continue;
                    }
                    members.retain(|member| !other.is_subtype_of(member));
                    members.push(other);
                }
            }
        }
        match members.len() {
            0 => Self::Any,
            1 => members.pop().expect("one member exists"),
            _ => {
                members.sort_by_key(ToString::to_string);
                Self::Intersection(members)
            }
        }
    }

    #[must_use]
    pub fn is_any(&self) -> bool {
        matches!(self, Self::Any)
    }

    #[must_use]
    pub fn is_never(&self) -> bool {
        matches!(self, Self::Never)
    }

    #[must_use]
    pub fn is_falsy(&self) -> bool {
        matches!(self, Self::Nil | Self::False)
    }

    #[must_use]
    pub fn is_nil(&self) -> bool {
        matches!(self, Self::Nil)
    }

    #[must_use]
    pub fn without(&self, excluded: &Self) -> Self {
        match self {
            Self::Any => Self::Any,
            Self::Union(members) => Self::union(members.iter().filter_map(|member| {
                if member.is_subtype_of(excluded) {
                    None
                } else {
                    Some(member.clone())
                }
            })),
            value if value.is_subtype_of(excluded) => Self::Never,
            _ => self.clone(),
        }
    }

    #[must_use]
    pub fn truthy_part(&self) -> Self {
        self.without(&Self::union([Self::Nil, Self::False]))
    }

    #[must_use]
    pub fn falsy_part(&self) -> Self {
        match self {
            Self::Any => Self::Any,
            Self::Union(members) => Self::union(members.iter().filter_map(|member| {
                if member.is_falsy() {
                    Some(member.clone())
                } else {
                    None
                }
            })),
            value if value.is_falsy() => value.clone(),
            _ => Self::Never,
        }
    }

    #[must_use]
    pub fn is_subtype_of(&self, expected: &Self) -> bool {
        if matches!(self, Self::Never) || matches!(expected, Self::Any) || matches!(self, Self::Any)
        {
            return true;
        }
        if self == expected {
            return true;
        }
        if let Self::Union(expected_members) = expected {
            return expected_members
                .iter()
                .any(|member| self.is_subtype_of(member));
        }
        if let Self::Union(actual_members) = self {
            return actual_members
                .iter()
                .all(|member| member.is_subtype_of(expected));
        }
        if let Self::Intersection(expected_members) = expected {
            return expected_members
                .iter()
                .all(|member| self.is_subtype_of(member));
        }
        if let Self::Intersection(actual_members) = self {
            return actual_members
                .iter()
                .any(|member| member.is_subtype_of(expected));
        }
        match (self, expected) {
            (Self::True, Self::Object)
            | (Self::False, Self::Object)
            | (Self::Nil, Self::Object)
            | (Self::Integer, Self::Object)
            | (Self::Float, Self::Object)
            | (Self::String, Self::Object)
            | (Self::Symbol, Self::Object)
            | (Self::Array(_), Self::Object)
            | (Self::Hash(_, _), Self::Object)
            | (Self::Named(_, _), Self::Object)
            | (Self::Proc(_, _), Self::Object) => true,
            (Self::Integer, Self::Named(name, args)) | (Self::Float, Self::Named(name, args))
                if name == "Numeric" && args.is_empty() =>
            {
                true
            }
            (Self::Named(_, _), Self::Named(name, args)) if name == "Object" && args.is_empty() => {
                true
            }
            (Self::Array(actual), Self::Array(expected)) => actual.is_subtype_of(expected),
            (Self::Hash(actual_key, actual_value), Self::Hash(expected_key, expected_value)) => {
                actual_key.is_subtype_of(expected_key) && actual_value.is_subtype_of(expected_value)
            }
            (
                Self::Proc(actual_params, actual_return),
                Self::Proc(expected_params, expected_return),
            ) => {
                actual_params.len() == expected_params.len()
                    && actual_params
                        .iter()
                        .zip(expected_params)
                        .all(|(actual, expected)| expected.is_subtype_of(actual))
                    && actual_return.is_subtype_of(expected_return)
            }
            (Self::Named(actual_name, actual_args), Self::Named(expected_name, expected_args)) => {
                actual_name == expected_name
                    && (expected_args.is_empty()
                        || (actual_args.len() == expected_args.len()
                            && actual_args
                                .iter()
                                .zip(expected_args)
                                .all(|(actual, expected)| actual.is_subtype_of(expected))))
            }
            (Self::TypeVar(actual), Self::TypeVar(expected)) => actual == expected,
            _ => false,
        }
    }

    fn is_definitely_disjoint_from(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (
                Self::Nil,
                Self::True
                    | Self::False
                    | Self::Integer
                    | Self::Float
                    | Self::String
                    | Self::Symbol
            ) | (
                Self::True,
                Self::Nil | Self::False | Self::Integer | Self::Float | Self::String | Self::Symbol
            ) | (
                Self::False,
                Self::Nil | Self::True | Self::Integer | Self::Float | Self::String | Self::Symbol
            ) | (
                Self::Integer,
                Self::Nil | Self::True | Self::False | Self::Float | Self::String | Self::Symbol
            ) | (
                Self::Float,
                Self::Nil | Self::True | Self::False | Self::Integer | Self::String | Self::Symbol
            ) | (
                Self::String,
                Self::Nil | Self::True | Self::False | Self::Integer | Self::Float | Self::Symbol
            ) | (
                Self::Symbol,
                Self::Nil | Self::True | Self::False | Self::Integer | Self::Float | Self::String
            )
        )
    }

    #[must_use]
    pub fn display(&self) -> String {
        self.to_string()
    }
}

/// A stateless facade for lattice operations, useful when embedding Typey in
/// another tool that wants to provide its own environment/worklist engine.
#[derive(Clone, Copy, Debug, Default)]
pub struct TypeLattice;

impl TypeLattice {
    #[must_use]
    pub const fn top(self) -> Type {
        Type::Any
    }

    #[must_use]
    pub const fn bottom(self) -> Type {
        Type::Never
    }

    #[must_use]
    pub fn join(self, left: &Type, right: &Type) -> Type {
        left.join(right)
    }

    #[must_use]
    pub fn meet(self, left: &Type, right: &Type) -> Type {
        left.meet(right)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Any => write!(f, "T.untyped"),
            Self::Never => write!(f, "T.noreturn"),
            Self::Nil => write!(f, "NilClass"),
            Self::True => write!(f, "TrueClass"),
            Self::False => write!(f, "FalseClass"),
            Self::Integer => write!(f, "Integer"),
            Self::Float => write!(f, "Float"),
            Self::String => write!(f, "String"),
            Self::Symbol => write!(f, "Symbol"),
            Self::Object => write!(f, "Object"),
            Self::Named(name, args) => {
                if args.is_empty() {
                    write!(f, "{name}")
                } else {
                    write!(f, "{name}[")?;
                    for (index, arg) in args.iter().enumerate() {
                        if index > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                    }
                    write!(f, "]")
                }
            }
            Self::Array(element) => write!(f, "T::Array[{element}]"),
            Self::Hash(key, value) => write!(f, "T::Hash[{key}, {value}]"),
            Self::Proc(params, result) => {
                write!(f, "T.proc")?;
                if !params.is_empty() {
                    write!(f, ".params(")?;
                    for (index, param) in params.iter().enumerate() {
                        if index > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{param}")?;
                    }
                    write!(f, ")")?;
                }
                write!(f, ".returns({result})")
            }
            Self::Intersection(members) => {
                write!(f, "T.all(")?;
                for (index, member) in members.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{member}")?;
                }
                write!(f, ")")
            }
            Self::Union(members) => {
                if members.len() == 2
                    && members.contains(&Self::True)
                    && members.contains(&Self::False)
                {
                    return write!(f, "T::Boolean");
                }
                if members.len() == 2 {
                    if let Some(other) = members.iter().find(|member| **member != Self::Nil) {
                        if members.contains(&Self::Nil) {
                            return write!(f, "T.nilable({other})");
                        }
                    }
                }
                write!(f, "T.any(")?;
                for (index, member) in members.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{member}")?;
                }
                write!(f, ")")
            }
            Self::TypeVar(name) => write!(f, "{name}"),
        }
    }
}
