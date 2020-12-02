use crate::{base_ty::BaseTy, literal::Literal, predicate::Predicate, variable::Variable};

use std::fmt;

#[derive(Clone, Debug)]
pub struct FuncTy<V> {
    arguments: Vec<Ty<V>>,
    return_ty: Box<Ty<V>>,
}

impl<V> FuncTy<V> {
    pub fn new(arguments: Vec<Ty<V>>, return_ty: Ty<V>) -> Self {
        Self {
            arguments,
            return_ty: Box::new(return_ty),
        }
    }

    pub fn arguments(&self) -> &[Ty<V>] {
        &self.arguments
    }

    pub fn return_ty(&self) -> &Ty<V> {
        &self.return_ty
    }

    pub fn shape_eq(&self, rhs: &Self) -> bool {
        self.arguments.len() == rhs.arguments.len()
            && self
                .arguments
                .iter()
                .zip(&rhs.arguments)
                .all(|(ty1, ty2)| ty1.shape_eq(ty2))
            && self.return_ty.shape_eq(&rhs.return_ty)
    }

    pub fn project_args(mut self, f: impl Fn(usize) -> Predicate<V> + Copy) -> Self {
        self.project(f, 0);
        self
    }

    fn project(&mut self, f: impl Fn(usize) -> Predicate<V> + Copy, index: usize) {
        for argument in &mut self.arguments {
            argument.project(f, index);
        }
        self.return_ty.project(f, index);
    }
}

impl<V: fmt::Display> fmt::Display for FuncTy<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut arguments = self.arguments.iter();

        write!(f, "fn(")?;
        if let Some(ty) = arguments.next() {
            write!(f, "{}", ty)?;
            for ty in arguments {
                write!(f, ", {}", ty)?;
            }
        }
        write!(f, ") -> {}", self.return_ty)
    }
}

#[derive(Clone, Debug)]
pub enum Ty<V> {
    Refined(BaseTy, Predicate<V>),
    Func(FuncTy<V>),
}

impl<V> Ty<V> {
    fn project(&mut self, f: impl Fn(usize) -> Predicate<V> + Copy, index: usize) {
        match self {
            Self::Refined(_, predicate) => predicate.project(f, index),
            Self::Func(func_ty) => func_ty.project(f, index + 1),
        }
    }

    pub fn shape_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Refined(b1, _), Self::Refined(b2, _)) => (b1 == b2),
            (Self::Func(func1), Self::Func(func2)) => func1.shape_eq(func2),
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

    pub fn selfify(self, var: V) -> Self {
        match self {
            Self::Refined(base_ty, predicate) => Self::Refined(
                base_ty,
                predicate & Predicate::from(Variable::Bounded).eq(base_ty, Variable::from(var)),
            ),
            ty => ty,
        }
    }

    pub fn singleton(literal: Literal) -> Self {
        let base_ty = literal.base_ty();

        Ty::Refined(
            base_ty,
            Predicate::from(Variable::Bounded).eq(base_ty, literal),
        )
    }
}

impl<V: fmt::Display> fmt::Display for Ty<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refined(base_ty, predicate) => {
                write!(f, "{{ b: {} | {} }}", base_ty, predicate)
            }
            Self::Func(func_ty) => func_ty.fmt(f),
        }
    }
}
