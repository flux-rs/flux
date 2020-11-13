use std::{
    fmt::{Display, Formatter, Result},
    ops::BitAnd,
};

use crate::{
    ir::Literal,
    replace::Replace,
    ty::{BaseTy, Predicate, Ty, Variable},
};

#[derive(Debug)]
pub enum Constraint {
    Pred(Predicate),
    And(Box<Self>, Box<Self>),
    // forall x : b. p => c
    ForAll(Variable, BaseTy, Predicate, Box<Self>),
}

impl Constraint {
    pub(super) fn forall(
        v: Variable,
        b: BaseTy,
        p: impl Into<Predicate>,
        c: impl Into<Self>,
    ) -> Self {
        let p = p.into();
        let c = c.into();

        match (&p, &c) {
            (_, Constraint::Pred(Predicate::Lit(Literal::Bool(true)))) => true.into(),
            _ => Self::ForAll(v, b, p, Box::new(c)),
        }
    }

    pub(super) fn implication(x: Variable, t: Ty, c: impl Into<Self>) -> Self {
        if let Ty::RefBase(v, b, mut p) = t {
            p.replace(v, x);
            Self::forall(x, b, p, c)
        } else {
            c.into()
        }
    }
}

impl<Rhs: Into<Constraint>> BitAnd<Rhs> for Constraint {
    type Output = Self;

    fn bitand(self, rhs: Rhs) -> Self::Output {
        let rhs = rhs.into();

        if let Constraint::Pred(Predicate::Lit(Literal::Bool(true))) = self {
            rhs
        } else if let Constraint::Pred(Predicate::Lit(Literal::Bool(true))) = rhs {
            self
        } else {
            Constraint::And(Box::new(self), Box::new(rhs))
        }
    }
}

impl From<bool> for Constraint {
    fn from(b: bool) -> Self {
        Self::Pred(b.into())
    }
}

impl From<Predicate> for Constraint {
    fn from(p: Predicate) -> Self {
        Self::Pred(p)
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Pred(pred) => pred.fmt(f),
            Self::And(c1, c2) => write!(f, "({} && {})", c1, c2),
            Self::ForAll(x, b, p, c) => write!(f, "(forall {}: {} . {} => {})", x, b, p, c),
        }
    }
}
