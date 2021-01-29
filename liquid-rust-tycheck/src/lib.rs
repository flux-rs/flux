#![feature(rustc_private)]

mod bblock_env;
mod check;
mod env;
mod glob_env;
mod result;
mod subtype;
mod synth;

use bblock_env::BBlockEnv;
use check::Check;
use env::Env;
use glob_env::GlobEnv;
use subtype::Subtype;

use liquid_rust_common::index::Index;
use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{
    ty::{LocalVariable, Predicate, Ty},
    BBlockId, Program,
};

pub fn check_program(program: &Program) {
    let genv = GlobEnv::new(program);
    let mut emitter = Emitter::new();

    for (func_id, func) in program.iter() {
        let input_env = Env::new(
            func.local_decls()
                .map(|(_, base_ty)| Ty::Refined(*base_ty, Predicate::Hole(genv.new_pred()))),
        );

        println!("Input env: {}", input_env);

        let bbenv = BBlockEnv::new(func, &genv, &mut emitter);

        let start_env = &bbenv.get_ty(BBlockId::start()).input;

        input_env.subtype(start_env, &mut emitter, ()).unwrap();

        let func_ty = func
            .ty()
            .clone()
            .project_args(|pos| Predicate::Var(LocalVariable::new(pos + 1).into()));

        let env = (&genv, &bbenv, func_ty.return_ty());

        for (bb_id, bb) in func.bblocks() {
            let bb_ty = bbenv.get_ty(bb_id);

            bb.check(bb_ty, &mut emitter, env).unwrap();
        }
    }

    emitter.emit();
}
