use crate::{env::Env, result::TyResult, subtype::Subtype};

use liquid_rust_common::index::Index;
use liquid_rust_ty::LocalVariable;

impl<'env, S> Subtype<'env, S> for Env {
    type Env = ();

    fn subtype(&self, other: &Self, (): Self::Env) -> TyResult<S> {
        let len_locals = self.len_locals();
        assert_eq!(len_locals, other.len_locals());

        let offset = self.len() - len_locals;

        let mut env = Env::empty(len_locals);

        let mut env1 = self.iter();
        let mut env2 = other.iter();

        while let Some((var1, ty1)) = env1.next() {
            if var1.index() < len_locals {
                while let Some((var2, ty2)) = env2.next() {
                    if var2.index() < len_locals {
                        assert_eq!(var1, var2);
                        ty1.subtype(ty2, &env)?;

                        env.bind(*var1, ty1.clone());

                        break;
                    } else {
                        let new_var2 = LocalVariable::new(var2.index() + offset);
                        let mut ty2 = ty2.clone();
                        ty2.map_variable(|var| {
                            if var.index() < len_locals {
                                var
                            } else {
                                LocalVariable::new(var.index() + offset)
                            }
                        });
                        env.bind(new_var2, ty2);
                    }
                }
            } else {
                env.bind(*var1, ty1.clone());
            }
        }

        Ok(())
    }
}
