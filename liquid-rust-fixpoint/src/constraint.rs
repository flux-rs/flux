use crate::{
    constant::Constant,
    emit,
    emit::{Ctx, Emit},
    pred::{Expr, Pred},
    sort::Sort,
};

use std::fmt;

pub enum Constraint {
    Pred(Pred),
    Conj(Vec<Self>),
    Guard(Pred, Box<Self>),
    ForAll(Sort, Pred, Box<Self>),
}

impl Constraint {
    pub const fn tru() -> Self {
        Self::Pred(Pred::Expr(Expr::Constant(Constant::Bool(true))))
    }
}

impl Emit for Constraint {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        match self {
            Self::Pred(pred) => emit!(w, ctx, "({})", pred),
            Self::Conj(preds) => {
                emit!(w, ctx, "(and")?;
                for pred in preds {
                    emit!(w, ctx, " {}", pred)?;
                }
                emit!(w, ctx, ")")
            }
            Self::ForAll(sort, premise, conclusion) => {
                emit!(
                    w,
                    &(*ctx + 1),
                    "(forall ((v{} {}) {}) {})",
                    ctx,
                    sort,
                    premise,
                    conclusion
                )
            }
            Self::Guard(premise, conclusion) => {
                emit!(w, ctx, "(forall ((_ int) {}) {})", premise, conclusion)
            }
        }
    }
}
