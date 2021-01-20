mod bblock_ty;
mod env;
mod ty;

use crate::result::TyResult;

use liquid_rust_fixpoint::Emitter;

pub(crate) trait Subtype<'env> {
    type Env: 'env;

    fn subtype(&self, other: &Self, emitter: &mut Emitter, env: Self::Env) -> TyResult;
}
