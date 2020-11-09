use crate::{
    ir::{BinOp, Literal, Local, UnOp},
    Generator,
};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BoundVariable(usize);

impl BoundVariable {
    pub fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Variable {
    Local(Local),
    Bounded(BoundVariable),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Uint(IntSize),
    Int(IntSize),
    Bool,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum IntSize {
    Size8,
    Size16,
    Size32,
    Size64,
    Size128,
    SizePtr,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Predicate {
    Var(Variable),
    Lit(Literal),
    BinApp(BinOp, Box<Self>, Box<Self>),
    UnApp(UnOp, Box<Self>),
    Cond(Box<Self>, Box<Self>, Box<Self>),
    App(Variable, Vec<Self>),
}

impl Predicate {
    pub const fn bool(b: bool) -> Self {
        Self::Lit(Literal::Bool(b))
    }
}

#[derive(Debug, Clone)]
pub enum Ty {
    RefBase(Variable, BaseTy, Predicate),
    RefFunc(Vec<(Variable, Self)>, Box<Self>),
}
