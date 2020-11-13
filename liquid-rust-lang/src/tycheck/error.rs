use crate::{
    ty::{BaseTy, Ty},
    tycheck::Constraint,
};

pub type TyResult<T> = Result<T, TyError>;

pub enum TyError {
    ArityMismatch(usize, usize),
    ExpectedRefFunc(Ty),
    BaseMismatch(BaseTy, BaseTy),
    UnsatConstraint(Constraint),
}
