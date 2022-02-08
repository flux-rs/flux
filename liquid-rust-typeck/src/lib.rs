#![feature(rustc_private, min_specialization, once_cell)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

mod checker;
pub mod global_env;
mod intern;
mod lowering;
mod pretty;
mod pure_ctxt;
mod subst;
pub mod ty;
mod type_env;

use std::{fs, io::Write};

use checker::Checker;
use global_env::GlobalEnv;
use liquid_rust_common::{config::CONFIG, errors::ErrorReported};
use liquid_rust_core::ir::Body;
use liquid_rust_fixpoint::{Fixpoint, FixpointResult, Safeness};
use pure_ctxt::PureCtxt;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub fn check<'tcx>(
    global_env: &GlobalEnv<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Result<(), ErrorReported> {
    let fn_sig = global_env.lookup_fn_sig(def_id);

    let bb_envs = Checker::infer(global_env, body, fn_sig)?;
    let (pure_cx, kvars) = Checker::check(global_env, body, fn_sig, bb_envs)?;

    if CONFIG.dump_constraint {
        dump_constraint(global_env.tcx, def_id, &pure_cx).unwrap();
    }

    let constraint = pure_cx.into_fixpoint(kvars);

    if CONFIG.dump_constraint {
        dump_fixpoint(global_env.tcx, def_id, &constraint).unwrap();
    }

    match Fixpoint::check(&constraint) {
        Ok(FixpointResult {
            tag: Safeness::Safe,
        }) => Ok(()),
        Ok(FixpointResult {
            tag: Safeness::Unsafe,
        }) => {
            global_env.tcx.sess.emit_err(errors::RefineError {
                span: body.mir.span,
            });
            Err(ErrorReported)
        }
        Ok(FixpointResult {
            tag: Safeness::Crash,
        }) => panic!("fixpoint crash"),
        Err(err) => panic!("failed to run fixpoint: {:?}", err),
    }
}

fn dump_constraint(tcx: TyCtxt, def_id: DefId, cx: &PureCtxt) -> Result<(), std::io::Error> {
    let dir = CONFIG.log_dir.join("horn");
    fs::create_dir_all(&dir)?;
    let mut file = fs::File::create(dir.join(tcx.def_path_str(def_id)))?;
    write!(file, "{:?}", cx)
}

fn dump_fixpoint(tcx: TyCtxt, def_id: DefId, fixpoint: &Fixpoint) -> Result<(), std::io::Error> {
    let dir = CONFIG.log_dir.join("horn");
    fs::create_dir_all(&dir)?;
    let mut file = fs::File::create(dir.join(format!("{}.smt2", tcx.def_path_str(def_id))))?;
    write!(file, "{}", fixpoint)
}

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefineError {
        #[message = "unsafe function"]
        #[label = "this function is unsafe"]
        pub span: Span,
    }
}
