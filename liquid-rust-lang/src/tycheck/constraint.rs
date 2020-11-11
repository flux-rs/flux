use crate::{
    replace::Replace,
    ty::{BaseTy, Predicate, Ty, Variable},
};

pub(super) enum Constraint {
    Pred(Predicate),
    Conj(Box<Self>, Box<Self>),
    // forall x : b. p => c
    Impl(Variable, BaseTy, Predicate, Box<Self>),
}

impl Constraint {
    pub(super) fn or(self, rhs: impl Into<Self>) -> Self {
        Constraint::Conj(Box::new(self), Box::new(rhs.into()))
    }

    pub(super) fn implication(x: Variable, t: Ty, c: Self) -> Self {
        if let Ty::RefBase(v, b, mut p) = t {
            p.replace(v, x);
            Self::Impl(x, b, p, Box::new(c))
        } else {
            c
        }
    }
}

impl From<bool> for Constraint {
    fn from(b: bool) -> Self {
        Self::Pred(b.into())
    }
}
