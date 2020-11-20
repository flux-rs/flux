mod predicate;

pub use predicate::Predicate;

use crate::generator::Generator;

pub use liquid_rust_common::ty::{BaseTy, IntSize};

use std::fmt::{Display, Formatter, Result};


#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
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

#[derive(Debug, Clone)]
pub enum Ty {
    Refined(Variable, BaseTy, Predicate),
    Func(Vec<(Variable, Self)>, Box<Self>),
}

impl Ty {
    pub fn selfify(self, var: Variable) -> Self {
        if let Self::Refined(x, base, pred) = self {
            Self::Refined(x, base, pred & Predicate::from(x).eq(var))
        } else {
            self
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Refined(var, base, pred) => write!(f, "{{ {}: {} | {} }}", var, base, pred),
            Self::Func(args, ret_ty) => {
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
