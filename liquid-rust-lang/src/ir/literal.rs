use std::fmt::{Display, Formatter, Result};

use crate::{ir::FuncId, ty::IntSize};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Literal {
    Bool(bool),
    Int(i128, IntSize),
    Uint(u128, IntSize),
    Unit,
    Fn(FuncId),
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<()> for Literal {
    fn from((): ()) -> Self {
        Self::Unit
    }
}

impl From<usize> for Literal {
    fn from(uint: usize) -> Self {
        Self::Uint(uint as u128, IntSize::SizePtr)
    }
}

impl From<isize> for Literal {
    fn from(int: isize) -> Self {
        Self::Int(int as i128, IntSize::SizePtr)
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Bool(b) => b.fmt(f),
            Self::Int(int, _) => int.fmt(f),
            Self::Uint(uint, _) => uint.fmt(f),
            Self::Unit => "unit".fmt(f),
            Self::Fn(func_id) => func_id.fmt(f),
        }
    }
}
