use std::fmt;

use crate::names::{Field, Location};

#[derive(Debug)]
pub enum Pred<S = usize> {
    Constant(Constant),
    Place(Place<S>),
    BinaryOp(BinOp, Box<Pred<S>>, Box<Pred<S>>),
    UnaryOp(UnOp, Box<Pred<S>>),
}
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Constant {
    Bool(bool),
    Int(u128),
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Int(n) => write!(f, "{}", n),
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub struct Place<S = usize> {
    pub base: Var<S>,
    pub projs: Vec<Proj>,
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.base)?;
        for proj in &self.projs {
            write!(f, ".{}", proj.0)?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum Var<S = usize> {
    Nu,
    Location(Location<S>),
    Field(Field<S>),
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Var::Nu => write!(f, "v"),
            Var::Location(l) => write!(f, "l${}", l.0),
            Var::Field(fld) => write!(f, "f${}", fld.0),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct Proj(pub usize);

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Iff,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Eq => write!(f, "="),
            BinOp::Ge => write!(f, ">="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Iff => write!(f, "<=>"),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum UnOp {
    Not,
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "¬"),
        }
    }
}
