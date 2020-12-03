use crate::{base_ty::BaseTy, literal::Literal, predicate::Predicate, variable::Variable};

use std::fmt;

/// A dependent function type: `fn(a_1: T_1, ..., a_n: T_n) -> T`.
///
/// The arguments `a_1`, ..., `a_n` are represented using de Bruijn indices inside the predicates.
#[derive(Clone, Debug)]
pub struct FuncTy<V> {
    /// The types of the function's arguments.
    arguments: Vec<Ty<V>>,
    /// The return type of the function.
    return_ty: Box<Ty<V>>,
}

impl<V> FuncTy<V> {
    /// Create a new dependent function type.
    pub fn new(arguments: Vec<Ty<V>>, return_ty: Ty<V>) -> Self {
        Self {
            arguments,
            return_ty: Box::new(return_ty),
        }
    }
    /// Return the types of the function's arguments.
    pub fn arguments(&self) -> &[Ty<V>] {
        &self.arguments
    }
    /// Return the return type of the function.
    pub fn return_ty(&self) -> &Ty<V> {
        &self.return_ty
    }
    /// Check if two function types have the same shape, i.e. if they have the same arity and their
    /// arguments and return types have the same shape.
    pub fn shape_eq(&self, rhs: &Self) -> bool {
        self.arguments.len() == rhs.arguments.len()
            && self
                .arguments
                .iter()
                .zip(&rhs.arguments)
                .all(|(ty1, ty2)| ty1.shape_eq(ty2))
            && self.return_ty.shape_eq(&rhs.return_ty)
    }
    /// Project the function's arguments into local variables and let untouched the arguments of
    /// any inner function type.
    pub fn project_args(mut self, f: impl Fn(usize) -> Predicate<V> + Copy) -> Self {
        self.project(f, 0);
        self
    }

    /// Project the arguments inside the type that have a specific index into local variables.
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

/// A refined type.
#[derive(Clone, Debug)]
pub enum Ty<V> {
    /// A refined base type: `{ b: B | p }`.
    Refined(BaseTy, Predicate<V>),
    /// A dependent function type.
    Func(FuncTy<V>),
}

impl<V> Ty<V> {
    /// Project the arguments inside the type that have a specific index into local variables.
    fn project(&mut self, f: impl Fn(usize) -> Predicate<V> + Copy, index: usize) {
        match self {
            Self::Refined(_, predicate) => predicate.project(f, index),
            // Increase the index by one when entering a nested function type.
            Self::Func(func_ty) => func_ty.project(f, index + 1),
        }
    }

    /// Check if two types have the same shape, i.e. if they are both refined types over the same
    /// base type or if they are both dependend function types with the same shape.
    pub fn shape_eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Refined(b1, _), Self::Refined(b2, _)) => (b1 == b2),
            (Self::Func(func1), Self::Func(func2)) => func1.shape_eq(func2),
            _ => false,
        }
    }

    /// Get the base type if the type is a refined base type. Return `None` otherwise.
    pub fn get_base(&self) -> Option<BaseTy> {
        if let Self::Refined(base_ty, _) = self {
            Some(*base_ty)
        } else {
            None
        }
    }

    /// Selfify the current type, i.e. if the current type is a refined base type `{b: B | p}`
    /// return `{b: B | p && (b = var)}`.
    pub fn selfify(self, var: V) -> Self {
        match self {
            Self::Refined(base_ty, predicate) => Self::Refined(
                base_ty,
                predicate & Predicate::from(Variable::Bound).eq(base_ty, Variable::from(var)),
            ),
            ty => ty,
        }
    }

    /// Return the singleton type for a literal.
    pub fn singleton(literal: Literal) -> Self {
        let base_ty = literal.base_ty();

        Ty::Refined(
            base_ty,
            Predicate::from(Variable::Bound).eq(base_ty, literal),
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
