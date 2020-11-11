use std::ops::Add;

use crate::{
    ir::{BinOp, Literal, UnOp},
    ty::Variable,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Predicate {
    Var(Variable),
    Lit(Literal),
    BinApp(BinOp, Box<Self>, Box<Self>),
    UnApp(UnOp, Box<Self>),
    Cond(Box<Self>, Box<Self>, Box<Self>),
    App(Variable, Vec<Self>),
}

impl From<bool> for Predicate {
    fn from(b: bool) -> Self {
        Self::Lit(b.into())
    }
}

impl<Rhs: Into<Predicate>> Add<Rhs> for Predicate {
    type Output = Self;

    fn add(self, rhs: Rhs) -> Self::Output {
        Self::Output::BinApp(BinOp::Add, Box::new(self), Box::new(rhs.into()))
    }
}
