use crate::{env::Env, result::TyResult, subtype::Subtype};

use liquid_rust_ty::Ty;

impl<'env, S> Subtype<'env, S> for Ty {
    type Env = &'env Env;

    fn subtype(&self, other: &Self, env: Self::Env) -> TyResult<S> {
        println!("{} ⊢ {} <: {}", env, self, other);
        Ok(())
    }
}
