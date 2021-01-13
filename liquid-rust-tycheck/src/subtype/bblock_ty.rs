use crate::{bblock_env::BBlockTy, result::TyResult, subtype::Subtype};

impl<'env, S> Subtype<'env, S> for BBlockTy {
    type Env = ();

    fn subtype(&self, other: &Self, (): Self::Env) -> TyResult<S> {
        other.input.subtype(&self.input, ())?;
        self.output.subtype(&other.input, ())
    }
}
