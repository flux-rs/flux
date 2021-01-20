mod bblock;
mod operand;
mod rvalue;
mod terminator;

use crate::result::TyResult;

use liquid_rust_fixpoint::Emitter;

pub(crate) trait Check<'ty, 'env> {
    type Ty: 'ty;
    type Env: 'env;

    fn check(&self, ty: Self::Ty, emitter: &mut Emitter, env: Self::Env) -> TyResult;
}
