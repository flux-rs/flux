use crate::{emit, emit::Emit, pred::Pred, sort::Sort, variable::Variable, Fixpoint};

use std::fmt;

pub enum Constraint {
    Pred(Pred),
    Conj(Vec<Self>),
    ForAll(Variable, Sort, Pred, Box<Self>),
}

impl Emit for Constraint {
    fn emit<W: fmt::Write>(&self, w: &mut W, fixpoint: &Fixpoint) -> fmt::Result {
        match self {
            Self::Pred(pred) => pred.emit(w, fixpoint),
            Self::Conj(preds) => {
                emit!(w, fixpoint, "(and")?;
                for pred in preds {
                    emit!(w, fixpoint, " {}", pred)?;
                }
                emit!(w, fixpoint, ")")
            }
            Self::ForAll(variable, sort, premise, conclusion) => {
                emit!(
                    w,
                    fixpoint,
                    "(forall (({} {}) {}) {})",
                    variable,
                    sort,
                    premise,
                    conclusion
                )
            }
        }
    }
}
