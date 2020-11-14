use std::{
    fmt::{Display, Formatter, Result},
    ops::{Add, BitAnd},
};

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
    App(Variable, Vec<Self>),
}

impl Predicate {
    pub fn eq(self, rhs: impl Into<Predicate>) -> Self {
        Self::BinApp(BinOp::Eq, Box::new(self), Box::new(rhs.into()))
    }
}

impl From<Variable> for Predicate {
    fn from(var: Variable) -> Self {
        Self::Var(var)
    }
}

impl From<Literal> for Predicate {
    fn from(lit: Literal) -> Self {
        Self::Lit(lit)
    }
}

impl From<bool> for Predicate {
    fn from(b: bool) -> Self {
        Self::Lit(b.into())
    }
}

impl<Rhs: Into<Predicate>> BitAnd<Rhs> for Predicate {
    type Output = Self;

    fn bitand(self, rhs: Rhs) -> Self::Output {
        Self::Output::BinApp(BinOp::And, Box::new(self), Box::new(rhs.into()))
    }
}

impl<Rhs: Into<Predicate>> Add<Rhs> for Predicate {
    type Output = Self;

    fn add(self, rhs: Rhs) -> Self::Output {
        Self::Output::BinApp(BinOp::Add, Box::new(self), Box::new(rhs.into()))
    }
}

impl Display for Predicate {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Var(var) => var.fmt(f),
            Self::Lit(lit) => lit.fmt(f),
            Self::BinApp(bin_op, op1, op2) => write!(f, "{} {} {}", op1, bin_op, op2),
            Self::UnApp(un_op, op1) => write!(f, "{}{}", un_op, op1),
            Self::App(func, args) => {
                let mut args = args.iter();
                if let Some(arg) = args.next() {
                    write!(f, "{}({}", func, arg)?;
                    for arg in args {
                        write!(f, ", {}", arg)?
                    }
                    write!(f, ")")
                } else {
                    write!(f, "{}()", func)
                }
            }
        }
    }
}
