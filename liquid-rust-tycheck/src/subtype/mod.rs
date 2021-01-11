mod bblock_ty;
mod env;
mod ty;

use crate::result::TyResult;

pub(crate) trait Subtype<'env, S> {
    type Env: 'env;

    fn subtype(&self, other: &Self, envs: Self::Env) -> TyResult<S>;
}
