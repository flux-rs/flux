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
use liquid_rust_mir::{BBlockId, Program};
use liquid_rust_ty::{LocalVariable, Predicate, Ty};

use std::fmt::Debug;

pub fn check_program<S: Clone + Debug>(program: &Program<S>) {
    let genv = GlobEnv::new(program);

    for (_, func) in program.iter() {
        let input_env = Env::new(
            func.local_decls()
                .map(|(_, base_ty)| Ty::Refined(*base_ty, genv.new_pred())),
        );

        println!("Input env: {}", input_env);

        let bbenv = BBlockEnv::new(func, &genv);

        let start_env = &bbenv.get_ty(BBlockId::start()).input;

        Subtype::<'_, S>::subtype(&input_env, start_env, ());

        let func_ty = func
            .ty()
            .clone()
            .project_args(|pos| Predicate::Var(LocalVariable::new(pos + 1).into()));

        let env = (&genv, &bbenv, func_ty.return_ty());

        for (bb_id, bb) in func.bblocks() {
            let bb_ty = bbenv.get_ty(bb_id);

            bb.check(bb_ty, env).unwrap();
        }
    }
}
