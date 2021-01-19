use crate::{env::Env, result::TyResult, subtype::Subtype};

use liquid_rust_common::index::{Index, IndexGen};
use liquid_rust_ty::{LocalVariable, Predicate, Ty, Variable};

impl<'env, S> Subtype<'env, S> for Env {
    type Env = ();

    fn subtype(&self, other: &Self, (): Self::Env) -> TyResult<S> {
        println!("\nSub-Env: {} <: {}", self, other);

        let len_locals = self.len_locals();
        assert_eq!(len_locals, other.len_locals());

        let mut env = Env::empty();

        let gen = IndexGen::<LocalVariable>::new();

        for _ in 0..len_locals {
            gen.generate();
        }

        let mut stack1 = vec![];
        let mut stack2 = vec![];

        if self.len_binds() == 0 {
            for (local, ty) in self.types() {
                stack1.push(((*local).into(), ty.clone()));
            }

            for (local, ty) in other.types() {
                stack2.push(((*local).into(), ty.clone()));
            }

            for (target, ty2) in other.binds().cloned() {
                if let Ty::Refined(base_ty, _) = &ty2 {
                    let target = target.into();
                    let new_local = gen.generate();

                    for (local, ty) in stack1.iter_mut() {
                        if *local == target {
                            *local = new_local;
                        }

                        ty.replace_variable(target.into(), new_local);
                    }

                    let ty1 = Ty::Refined(
                        *base_ty,
                        Predicate::Var(Variable::Bound)
                            .eq(*base_ty, Predicate::Var(Variable::Local(new_local))),
                    );

                    stack1.push((target, ty1));

                    let new_local = gen.generate();

                    for (local, ty) in stack2.iter_mut() {
                        if *local == target {
                            *local = new_local;
                        }

                        ty.replace_variable(target.into(), new_local);
                    }

                    stack2.push((target, ty2.clone()));
                } else {
                    panic!()
                }
            }
        } else if other.len_binds() == 0 {
            for (local, ty) in self.types() {
                stack1.push(((*local).into(), ty.clone()));
            }

            for (local, ty) in other.types() {
                stack2.push(((*local).into(), ty.clone()));
            }

            for (target, ty1) in self.binds().cloned() {
                if let Ty::Refined(base_ty, _) = &ty1 {
                    let target = target.into();
                    let new_local = gen.generate();

                    for (local, ty) in stack2.iter_mut() {
                        if *local == target {
                            *local = new_local;
                        }

                        ty.replace_variable(target.into(), new_local);
                    }

                    let ty2 = Ty::Refined(
                        *base_ty,
                        Predicate::Var(Variable::Bound)
                            .eq(*base_ty, Predicate::Var(Variable::Local(new_local))),
                    );

                    stack2.push((target, ty2));

                    let new_local = gen.generate();

                    for (local, ty) in stack1.iter_mut() {
                        if *local == target {
                            *local = new_local;
                        }

                        ty.replace_variable(target.into(), new_local);
                    }

                    stack1.push((target, ty1.clone()));
                } else {
                    panic!()
                }
            }
        } else {
            panic!()
        }

        let mut stack1 = stack1.into_iter();
        let mut stack2 = stack2.into_iter();

        while let Some((var1, ty1)) = stack1.next() {
            if var1.index() < len_locals {
                while let Some((var2, ty2)) = stack2.next() {
                    if var2.index() < len_locals {
                        assert_eq!(var1, var2);
                        ty1.subtype(&ty2, &env)?;

                        env.bind(var1, ty1.clone());

                        break;
                    } else {
                        env.bind(var2, ty2);
                    }
                }
            } else {
                env.bind(var1, ty1.clone());
            }
        }

        Ok(())
    }
}
