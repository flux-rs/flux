pub use liquid_rust_core::{
    names::Field,
    ty::{
        pred::{self, Constant},
        BaseTy,
    },
};

use std::{
    fmt,
    hash::{Hash, Hasher},
};

/// The span of each AST item, relative to the beginning of the outermost type in the AST.
pub type Span = std::ops::Range<usize>;

/// The AST representation of an identifier
#[derive(Debug, Clone)]
pub struct Ident<'source> {
    pub symbol: &'source str,
    pub span: Span,
}

impl<'source> PartialEq for Ident<'source> {
    fn eq(&self, other: &Self) -> bool {
        self.symbol == other.symbol
    }
}

impl<'source> Eq for Ident<'source> {}

impl<'source> Hash for Ident<'source> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
    }
}

impl<'source> fmt::Display for Ident<'source> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {:?}", self.symbol, self.span)
    }
}

/// The AST representation of a place
#[derive(Debug, Clone)]
pub struct Place<'source> {
    pub place: pred::Place<Ident<'source>>,
    pub span: Span,
}

/// The AST representation of unary operators over predicates.
#[derive(Debug, Clone)]
pub struct UnOp {
    pub kind: UnOpKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub enum UnOpKind {
    /// The `!` operator.
    Not,
    /// The `-` operator.
    Neg,
}

/// The AST representation of binary operators between predicates.
#[derive(Debug, Clone)]
pub struct BinOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOpKind {
    /// The `+` operator.
    Add,
    /// The `-` operator.
    Sub,
    /// The `*` operator.
    Mul,
    /// The `/` operator.
    Div,
    /// The `%` operator.
    Rem,
    /// The `&&` operator.
    And,
    /// The `||` operator.
    Or,
    /// The `==` operator.
    Eq,
    /// The `!=` operator.
    Neq,
    /// The `<` operator.
    Lt,
    /// The `>` operator.
    Gt,
    /// The `<=` operator.
    Le,
    /// The `>=` operator.
    Ge,
}

/// The AST representation of a quantifier-free predicate.
#[derive(Debug, Clone)]
pub struct Predicate<'source> {
    pub kind: PredicateKind<'source>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum PredicateKind<'source> {
    /// A literal.
    Lit(Constant),
    /// A place.
    Place(Place<'source>),
    /// An unary operation between predicates.
    UnaryOp(UnOp, Box<Predicate<'source>>),
    /// A binary operation between predicates.
    BinaryOp(BinOp, Box<Predicate<'source>>, Box<Predicate<'source>>),
}

/// The AST representation of a function type
#[derive(Debug, Clone)]
pub struct FnTy<'source> {
    pub kind: FnTyInner<'source>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FnTyInner<'source> {
    pub args: Vec<(Ident<'source>, Ty<'source>)>,
    pub output: Box<Ty<'source>>,
}

/// The AST representation of a refinement type.
#[derive(Debug, Clone)]
pub struct Ty<'source> {
    pub kind: TyKind<'source>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TyKind<'source> {
    /// An unrefined base type.
    Base(BaseTy),
    /// A refined base type.
    Refined(Option<Ident<'source>>, BaseTy, Predicate<'source>),
    /// A dependent product type.
    Tuple(Vec<(Field<Ident<'source>>, Ty<'source>)>),
}
