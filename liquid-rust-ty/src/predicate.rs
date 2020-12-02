use crate::{
    literal::Literal,
    op::{BinOp, UnOp},
    variable::Variable,
    BaseTy,
};

use std::{fmt, ops::BitAnd};

#[derive(Clone, Debug)]
pub enum Predicate<V> {
    Lit(Literal),
    Var(Variable<V>),
    UnApp(UnOp, Box<Self>),
    BinApp(BinOp, Box<Self>, Box<Self>),
}

impl<V> Predicate<V> {
    pub fn map<W>(self, f: impl Fn(V) -> W + Copy) -> Predicate<W> {
        match self {
            Self::Lit(literal) => Predicate::Lit(literal),
            Self::Var(variable) => Predicate::Var(match variable {
                Variable::Free(var) => Variable::Free(f(var)),
                Variable::Bounded => Variable::Bounded,
                Variable::Arg(_) => unreachable!(),
            }),
            Self::UnApp(un_op, op) => Predicate::UnApp(un_op, Box::new(op.map(f))),
            Self::BinApp(bin_op, op1, op2) => {
                Predicate::BinApp(bin_op, Box::new(op1.map(f)), Box::new(op2.map(f)))
            }
        }
    }

    pub fn eq(self, base_ty: BaseTy, rhs: impl Into<Self>) -> Self {
        Self::BinApp(BinOp::Eq(base_ty), Box::new(self), Box::new(rhs.into()))
    }

    pub fn neq(self, base_ty: BaseTy, rhs: impl Into<Self>) -> Self {
        Self::BinApp(BinOp::Neq(base_ty), Box::new(self), Box::new(rhs.into()))
    }

    pub(crate) fn project(&mut self, f: impl Fn(usize) -> Predicate<V> + Copy, index: usize) {
        match self {
            Self::Lit(_) => (),
            Self::Var(variable) => match variable {
                Variable::Free(_) | Variable::Bounded => (),
                Variable::Arg(arg) => {
                    if arg.index() == index {
                        *self = f(arg.pos());
                    }
                }
            },
            Self::UnApp(_, op) => op.project(f, index),
            Self::BinApp(_, op1, op2) => {
                op1.project(f, index);
                op2.project(f, index);
            }
        }
    }
}

impl<V, Rhs: Into<Predicate<V>>> BitAnd<Rhs> for Predicate<V> {
    type Output = Self;
    fn bitand(self, rhs: Rhs) -> Self {
        match (self, rhs.into()) {
            (Self::Lit(lit), rhs) if lit.is_true() => rhs,
            (lhs, Self::Lit(lit)) if lit.is_true() => lhs,
            (lhs, rhs) => Self::BinApp(BinOp::And, Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl<V> From<Variable<V>> for Predicate<V> {
    fn from(variable: Variable<V>) -> Self {
        Self::Var(variable)
    }
}

impl<V> From<bool> for Predicate<V> {
    fn from(b: bool) -> Self {
        Self::Lit(b.into())
    }
}

impl<V> From<Literal> for Predicate<V> {
    fn from(literal: Literal) -> Self {
        Self::Lit(literal)
    }
}

impl<V: fmt::Display> fmt::Display for Predicate<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lit(literal) => literal.fmt(f),
            Self::Var(variable) => variable.fmt(f),
            Self::UnApp(un_op, op) => write!(f, "{}{}", un_op, op),
            Self::BinApp(bin_op, op1, op2) => write!(f, "({} {} {})", op1, bin_op, op2),
        }
    }
}
