use crate::{
    env::Env,
    result::{TyError, TyErrorKind, TyResult},
    subtype::Subtype,
};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, DUMMY_SP};

impl<'env> Subtype<'env> for Ty {
    type Env = &'env Env;

    fn subtype(&self, other: &Self, emitter: &mut Emitter, env: Self::Env) -> TyResult {
        println!("{} ⊢ {} <: {}", env, self, other);

        match (self, other) {
            (Ty::Refined(base_ty1, pred1), Ty::Refined(base_ty2, pred2)) => {
                if base_ty1 == base_ty2 {
                    emitter.add_constraint(
                        vec![],
                        *base_ty1,
                        pred1.clone(),
                        pred2.clone(),
                        DUMMY_SP,
                    );
                } else {
                    return Err(TyError {
                        kind: TyErrorKind::BaseMismatch {
                            expected: *base_ty1,
                            found: other.clone(),
                        },
                        span: DUMMY_SP,
                    });
                }
            }
            _ => todo!(),
        }

        Ok(())
    }
}
