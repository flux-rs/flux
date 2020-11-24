use crate::Ty;

use liquid_rust_common::ty::BaseTy;

pub type TyResult<T = ()> = Result<T, TyError>;

#[derive(Debug)]
pub enum TyError {
    BaseMismatch(BaseTy, BaseTy),
    ShapeMismatch(Ty, Ty),
}
