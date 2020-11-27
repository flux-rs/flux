use crate::{
    literal::Literal,
    op::{BinOp, UnOp},
    variable::Variable,
    BaseTy,
};

use std::{fmt, ops::BitAnd};

#[derive(Clone, Debug)]
pub enum Predicate<A> {
    Lit(Literal),
    Var(Variable<A>),
    UnApp(UnOp, Box<Self>),
    BinApp(BinOp, Box<Self>, Box<Self>),
}

impl<A> Predicate<A> {
    pub fn map<B>(self, f: impl Fn(A) -> B + Clone) -> Predicate<B> {
        match self {
            Self::Lit(literal) => Predicate::Lit(literal),
            Self::Var(variable) => Predicate::Var(variable.map(f)),
            Self::UnApp(un_op, op) => Predicate::UnApp(un_op, Box::new(op.map(f))),
            Self::BinApp(bin_op, op1, op2) => {
                Predicate::BinApp(bin_op, Box::new(op1.map(f.clone())), Box::new(op2.map(f)))
            }
        }
    }

    pub(crate) fn eq(self, base_ty: BaseTy, rhs: impl Into<Self>) -> Self {
        Self::BinApp(BinOp::Eq(base_ty), Box::new(self), Box::new(rhs.into()))
    }
}

impl<A, Rhs: Into<Predicate<A>>> BitAnd<Rhs> for Predicate<A> {
    type Output = Self;
    fn bitand(self, rhs: Rhs) -> Self {
        match (self, rhs.into()) {
            (Self::Lit(lit), rhs) if lit.is_true() => rhs,
            (lhs, Self::Lit(lit)) if lit.is_true() => lhs,
            (lhs, rhs) => Self::BinApp(BinOp::And, Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl<A> From<Variable<A>> for Predicate<A> {
    fn from(variable: Variable<A>) -> Self {
        Self::Var(variable)
    }
}

impl<A> From<bool> for Predicate<A> {
    fn from(b: bool) -> Self {
        Self::Lit(b.into())
    }
}

impl<A> From<Literal> for Predicate<A> {
    fn from(literal: Literal) -> Self {
        Self::Lit(literal)
    }
}

impl<A: fmt::Display> fmt::Display for Predicate<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lit(literal) => literal.fmt(f),
            Self::Var(variable) => variable.fmt(f),
            Self::UnApp(un_op, op) => write!(f, "{}{}", un_op, op),
            Self::BinApp(bin_op, op1, op2) => write!(f, "({} {} {})", op1, bin_op, op2),
        }
    }
}
