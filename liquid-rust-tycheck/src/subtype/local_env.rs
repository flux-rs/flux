use crate::{local_env::LocalEnv, subtype::Subtype};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::ty::{Predicate, Ty, Variable};

impl<'env> Subtype<'env> for LocalEnv {
    type Env = &'env mut Emitter;

    fn subtype(mut self, mut other: Self, emitter: Self::Env) {
        let mut env = self.spawn_empty();

        println!("Sub-Env: {} <: {}", self, other);

        loop {
            match (self.first(), other.first()) {
                (Some(var1), Some(var2)) => match (var1, var2) {
                    (Variable::Local(l1), Variable::Local(l2)) => {
                        if l1 == l2 {
                            let (_, ty1) = self.remove_first();
                            let (_, ty2) = other.remove_first();

                            ty1.subtype(&ty2, (&env, emitter));
                            env.bind(var1, ty1);
                        } else {
                            match other.first_ty().unwrap() {
                                Ty::Refined(base_ty, _) => {
                                    let base_ty = *base_ty;
                                    other.rebind(
                                        var2,
                                        Ty::Refined(
                                            base_ty,
                                            Predicate::Bound.eq(base_ty, Predicate::Var(var2)),
                                        ),
                                    )
                                }
                                Ty::Func(_) => panic!(),
                            }
                        }
                    }
                    (Variable::Ghost(_), var2) => {
                        assert_ne!(var1, var2);
                        let (var1, ty1) = self.remove_first();
                        env.bind(var1, ty1);
                    }
                    (var1, Variable::Ghost(_)) => {
                        assert_ne!(var1, var2);
                        let (var2, ty2) = other.remove_first();
                        env.bind(var2, ty2);
                    }
                },
                (None, None) => break,
                (Some(_), None) => {
                    let (var1, ty1) = self.remove_first();
                    env.bind(var1, ty1);
                }
                (None, Some(_)) => {
                    let (var2, ty2) = self.remove_first();
                    env.bind(var2, ty2);
                }
            }
        }
    }
}
