use crate::{local_env::LocalEnv, subtype::Subtype};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, DUMMY_SP};

impl<'env> Subtype<'env> for &Ty {
    type Env = (&'env LocalEnv, &'env mut Emitter);

    fn subtype(self, other: Self, (env, emitter): Self::Env) {
        match (self, other) {
            (Ty::Refined(base_ty1, pred1), Ty::Refined(base_ty2, pred2)) => {
                assert_eq!(base_ty1, base_ty2);
                for (variable, ty) in env.iter() {
                    emitter.add_bind(*variable, ty);
                }
                emitter
                    .add_constraint(*base_ty1, pred1.clone(), pred2.clone(), DUMMY_SP)
                    .unwrap();
                emitter.clear();
            }
            _ => todo!(),
        }
    }
}
