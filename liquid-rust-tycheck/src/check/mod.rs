mod bblock;
mod operand;
mod rvalue;
mod terminator;

use crate::result::TyResult;

pub(crate) trait Check<'ty, 'env, S> {
    type Ty: 'ty;
    type Env: 'env;

    fn check(&self, ty: Self::Ty, env: Self::Env) -> TyResult<S>;
}
