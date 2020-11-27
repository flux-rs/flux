use crate::{
    argument::Argument, base_ty::BaseTy, literal::Literal, predicate::Predicate, variable::Variable,
};

use std::fmt;

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
