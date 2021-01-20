mod bblock_ty;
mod env;
mod ty;

use crate::result::TyResult;

pub(crate) trait Subtype<'env> {
    type Env: 'env;

    fn subtype(&self, other: &Self, env: Self::Env) -> TyResult;
}
