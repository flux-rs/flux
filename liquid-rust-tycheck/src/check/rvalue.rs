use crate::{check::Check, env::Env, result::TyResult, subtype::Subtype, synth::Synth};

use liquid_rust_common::index::IndexGen;
use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{
    ty::{LocalVariable, Predicate, Ty, Variable},
    Rvalue,
};

impl<'ty, 'env> Check<'ty, 'env> for Rvalue {
    type Ty = &'ty Ty;
    type Env = &'env Env;

    fn check(&self, ty: Self::Ty, emitter: &mut Emitter, env: Self::Env) -> TyResult {
        let synth_ty = self.synth(env)?;

        let mut ty = ty.clone();

        let len_locals = env.len_locals();

        let gen = IndexGen::<LocalVariable>::new();

        for _ in 0..len_locals {
            gen.generate();
        }

        let mut stack = vec![];

        for (local, ty) in env.types() {
            stack.push(((*local).into(), ty.clone()));
        }

        for (target, bind_ty) in env.binds().cloned() {
            if let Ty::Refined(base_ty, _) = &bind_ty {
                let target = target.into();
                let new_local = gen.generate();

                for (local, ty) in stack.iter_mut() {
                    if *local == target {
                        *local = new_local;
                    }

                    ty.replace_variable(target.into(), new_local);
                }

                ty.replace_variable(target.into(), new_local);

                let ty = Ty::Refined(
                    *base_ty,
                    Predicate::Var(Variable::Bound)
                        .eq(*base_ty, Predicate::Var(Variable::Local(new_local))),
                );

                stack.push((target, ty));
            } else {
                panic!()
            }
        }

        for (var, ty) in stack {
            match &ty {
                Ty::Refined(base_ty, pred) => {
                    emitter.add_bind(var, *base_ty, pred);
                }
                _ => panic!(),
            }
        }

        synth_ty.subtype(&ty, emitter, ())?;

        emitter.clear();

        Ok(())
    }
}
