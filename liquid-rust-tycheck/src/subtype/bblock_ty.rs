use crate::{bblock_env::BBlockTy, result::TyResult, subtype::Subtype};

impl<'env> Subtype<'env> for BBlockTy {
    type Env = ();

    fn subtype(&self, other: &Self, env: Self::Env) -> TyResult {
        other.input.subtype(&self.input, env)?;
        self.output.subtype(&other.input, env)
    }
}
