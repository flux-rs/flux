//! Types used to represent liquid rust's AST.
mod ident;
mod op;
mod predicate;
mod ty;

pub use ident::Ident;
pub use op::{BinOp, BinOpKind, UnOp, UnOpKind};
pub use predicate::{Predicate, PredicateKind};
pub use ty::{Ty, TyKind};

/// The span of each AST item, relative to the beginning of the outermost type in the AST.
pub type Span = std::ops::Range<usize>;
