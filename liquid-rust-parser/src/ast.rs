pub use liquid_rust_common::{
    literal::{IntSize, Literal},
    op::{BinOp, UnOp},
};
pub use liquid_rust_ty::BaseTy;

use std::ops::Range;

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct Variable<'source>(pub(crate) &'source str, pub(crate) Range<usize>);

#[derive(Debug)]
pub enum Predicate<'source> {
    Var(Variable<'source>),
    Lit(Literal),
    BinApp(BinOp, Box<Self>, Box<Self>),
    UnApp(UnOp, Box<Self>),
}

#[derive(Debug)]
pub enum Ty<'source> {
    Base(BaseTy),
    Refined(Variable<'source>, BaseTy, Predicate<'source>),
    Func(Vec<(Variable<'source>, Self)>, Box<Self>),
}
