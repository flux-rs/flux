pub use crate::refinements::common::{Literal, BinOp, UnOp, BaseTy, IntSize};

#[derive(Debug)]
pub struct Variable(pub String);

#[derive(Debug)]
pub enum Predicate {
    Var(Variable),
    Lit(Literal),
    BinApp(BinOp, Box<Self>, Box<Self>),
    UnApp(UnOp, Box<Self>),
    Cond(Box<Self>, Box<Self>, Box<Self>),
    App(Variable, Vec<Self>),
}

#[derive(Debug)]
pub enum RefinedTy {
    Base(BaseTy),
    RefBase(Variable, BaseTy, Predicate),
    RefFunc(Vec<(Variable, Self)>, Box<Self>),
}

