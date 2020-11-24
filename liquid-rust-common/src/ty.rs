use crate::{
    index::Index,
    ir::{BinOp, Literal, Local, UnOp},
};

use std::{fmt, ops::BitAnd};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Unit,
    Bool,
    Uint(IntSize),
    Int(IntSize),
}

impl BaseTy {
    pub fn refined<A>(self) -> Ty<A> {
        Ty::Refined(self, true.into())
    }
}

impl fmt::Display for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => "()".fmt(f),
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

impl fmt::Display for IntSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = match self {
            Self::Size8 => "8",
            Self::Size16 => "16",
            Self::Size32 => "32",
            Self::Size64 => "64",
            Self::Size128 => "128",
            Self::SizePtr => "size",
        };

        slice.fmt(f)
    }
}
#[derive(Clone, Copy, Debug)]
pub struct Argument {
    pos: usize,
    level: usize,
}

impl Argument {
    pub fn new(pos: usize, level: usize) -> Self {
        Self { pos, level }
    }

    pub fn as_local(&self) -> Result<Local, usize> {
        match self.level {
            0 => Ok(Local::constructor(self.pos + 1)),
            level => Err(level),
        }
    }
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "arg_{}_{}", self.pos, self.level)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Variable<A> {
    Free(A),
    Bounded,
}

impl<A> Variable<A> {
    pub fn map<B>(self, f: impl Fn(A) -> B) -> Variable<B> {
        match self {
            Self::Bounded => Variable::Bounded,
            Self::Free(a) => Variable::Free(f(a)),
        }
    }
}

impl<A> From<A> for Variable<A> {
    fn from(free_variable: A) -> Self {
        Self::Free(free_variable)
    }
}

impl<A: fmt::Display> fmt::Display for Variable<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Free(a) => a.fmt(f),
            Self::Bounded => "b".fmt(f),
        }
    }
}

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

    pub fn eq(self, rhs: impl Into<Self>) -> Self {
        let rhs = rhs.into();
        Self::BinApp(BinOp::Eq, Box::new(self), Box::new(rhs))
    }
}

impl<A, Rhs: Into<Predicate<A>>> BitAnd<Rhs> for Predicate<A> {
    type Output = Self;
    fn bitand(self, rhs: Rhs) -> Self {
        match (self, rhs.into()) {
            (Self::Lit(Literal::Bool(true)), rhs) => rhs,
            (lhs, Self::Lit(Literal::Bool(true))) => lhs,
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

#[derive(Clone, Debug)]
pub enum Ty<A = Argument> {
    Refined(BaseTy, Predicate<A>),
    Func(Vec<(A, Ty)>, Box<Ty>),
}

impl<A> Ty<A> {
    pub fn map<B>(self, f: impl Fn(A) -> B + Clone) -> Ty<B> {
        match self {
            Self::Refined(base_ty, predicate) => Ty::Refined(base_ty, predicate.map(f)),
            Self::Func(arguments, return_ty) => Ty::Func(
                arguments
                    .into_iter()
                    .map(|(argument, ty)| {
                        let argument = f(argument);
                        (argument, ty)
                    })
                    .collect(),
                return_ty,
            ),
        }
    }

    pub fn shape_eq<B>(&self, rhs: &Ty<B>) -> bool {
        match (self, rhs) {
            (Self::Refined(b1, _), Ty::Refined(b2, _)) => (b1 == b2),
            (Self::Func(args1, ret1), Ty::Func(args2, ret2)) => {
                args1.len() == args2.len()
                    && args1
                        .iter()
                        .zip(args2)
                        .all(|((_, ty1), (_, ty2))| ty1.shape_eq(ty2))
                    && ret1.shape_eq(ret2)
            }
            _ => false,
        }
    }

    pub fn get_base(&self) -> Option<BaseTy> {
        if let Self::Refined(base_ty, _) = self {
            Some(*base_ty)
        } else {
            None
        }
    }

    pub fn selfify(self, var: A) -> Self {
        match self {
            Self::Refined(base_ty, predicate) => Self::Refined(
                base_ty,
                predicate & (Predicate::from(Variable::Bounded).eq(Variable::from(var))),
            ),
            ty => ty,
        }
    }
}

impl<A: fmt::Display> fmt::Display for Ty<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refined(base_ty, predicate) => {
                write!(f, "{{ b: {} | {} }}", base_ty, predicate)
            }
            Self::Func(arguments, return_ty) => {
                let mut arguments = arguments.iter();

                write!(f, "fn(")?;
                if let Some((argument, ty)) = arguments.next() {
                    write!(f, "{}: {}", argument, ty)?;
                    for (argument, ty) in arguments {
                        write!(f, ", {}: {}", argument, ty)?;
                    }
                }
                write!(f, ") -> {}", return_ty)
            }
        }
    }
}
