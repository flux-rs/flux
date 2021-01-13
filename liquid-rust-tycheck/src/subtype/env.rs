use crate::{env::Env, result::TyResult, subtype::Subtype};

impl<'env, S> Subtype<'env, S> for Env {
    type Env = ();

    fn subtype(&self, other: &Self, (): Self::Env) -> TyResult<S> {
        println!("{} <: {}", self, other);
        Ok(())
    }
}
