#![feature(rustc_private)]

mod bblock_env;
mod check;
mod func_env;
mod local_env;
mod subtype;
mod synth;

use bblock_env::BBlockEnv;
use check::Check;
use func_env::FuncEnv;
use local_env::LocalEnv;
use subtype::Subtype;

use liquid_rust_common::index::{Index, IndexGen};
use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{
    ty::{HoleId, Predicate, Ty, Variable},
    BBlockId, Local, Program,
};

use std::{collections::BTreeMap, rc::Rc};

pub fn check_program(program: &Program) {
    let func_env = FuncEnv::new(program.iter().map(|(_, func)| func.ty().clone()));
    let ghost_gen = Rc::new(IndexGen::new());

    let hole_gen = IndexGen::<HoleId>::new();

    let mut emitter = Emitter::new();

    for (_func_id, func) in program.iter() {
        if func.user_ty() {
            let local_gen = IndexGen::<Local>::new();

            let ret_local = local_gen.generate();

            let mut init_env = LocalEnv::empty(Rc::clone(&ghost_gen));

            let mut binds = BTreeMap::new();

            let func_ty = func
                .ty()
                .clone()
                .project_args(|pos| Predicate::Var(Variable::Local(Local::new(pos + 1))));

            let return_ty = func_ty.return_ty();

            for arg_ty in func_ty.arguments() {
                let arg = Variable::Local(local_gen.generate());
                let id = emitter.add_bind(arg, arg_ty);
                init_env.bind(arg, arg_ty.clone());
                binds.insert(arg, id);
            }

            let ret_ty = func.return_ty().refined();
            let ret_var = Variable::Local(ret_local);
            let id = emitter.add_bind(ret_var, &ret_ty);
            init_env.bind(ret_var, ret_ty);
            binds.insert(ret_var, id);

            for (local, local_ty) in func.temporaries() {
                let local = Variable::Local(local);
                let local_ty = local_ty.refined();
                let id = emitter.add_bind(local, &local_ty);
                init_env.bind(local, local_ty);
                binds.insert(local, id);
            }

            let mut bb_env = BBlockEnv::new();

            for _ in func.bblocks() {
                let mut env = LocalEnv::empty(Rc::clone(&ghost_gen));

                for (variable, init_ty) in init_env.iter() {
                    if let Ty::Refined(base_ty, _) = init_ty {
                        let hole_id = hole_gen.generate();
                        let ty = Ty::Refined(*base_ty, Predicate::Hole(hole_id.into()));
                        env.bind(*variable, ty);
                        let bind_id = binds[variable];
                        emitter.add_wf(*base_ty, hole_id, bind_id).unwrap();
                    } else {
                        panic!()
                    }
                }

                bb_env.insert(env);
            }

            let bb0_env = bb_env.get_ty(BBlockId::start()).unwrap().clone();

            init_env.subtype(bb0_env, &mut emitter);

            for (bb_id, bb) in func.bblocks() {
                let ty = bb_env.get_ty(bb_id).unwrap().clone();
                println!("{}: {}", bb_id, ty);
                bb.check(ty, (&func_env, &bb_env, return_ty, &mut emitter));
            }
        }
    }
    emitter.emit().unwrap();
}
