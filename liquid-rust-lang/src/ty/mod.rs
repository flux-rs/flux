mod predicate;

pub use predicate::Predicate;

use std::fmt::{Display, Formatter, Result};

use crate::generator::Generator;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Variable(usize);

impl Variable {
    pub fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "x{}", self.0)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Unit,
    Bool,
    Uint(IntSize),
    Int(IntSize),
}

impl Display for BaseTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unit => "Unit".fmt(f),
            Self::Bool => "bool".fmt(f),
            Self::Uint(size) => write!(f, "u{}", size),
            Self::Int(size) => write!(f, "i{}", size),
        }
    }
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

impl Display for IntSize {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let s = match self {
            Self::Size8 => "8",
            Self::Size16 => "16",
            Self::Size32 => "32",
            Self::Size64 => "64",
            Self::Size128 => "128",
            Self::SizePtr => "size",
        };

        s.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub enum Ty {
    RefBase(Variable, BaseTy, Predicate),
    RefFunc(Vec<(Variable, Self)>, Box<Self>),
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::RefBase(var, base, pred) => write!(f, "{{ {}: {} | {} }}", var, base, pred),
            Self::RefFunc(args, ret_ty) => {
                let mut args = args.iter();
                if let Some((arg, arg_ty)) = args.next() {
                    write!(f, "fn({}: {}", arg, arg_ty)?;
                    for (arg, arg_ty) in args {
                        write!(f, ", {}: {}", arg, arg_ty)?;
                    }
                    write!(f, ") -> {}", ret_ty)
                } else {
                    write!(f, "fn() -> {}", ret_ty)
                }
            }
        }
    }
}
