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
mod constraint_builder;
pub mod global_env;
mod intern;
mod lowering;
mod pretty;
pub mod ty;
mod type_env;

use checker::Checker;
use global_env::GlobalEnv;
use liquid_rust_common::errors::ErrorReported;
use liquid_rust_core::{ir::Body, ty as core};
use liquid_rust_fixpoint::{Fixpoint, FixpointResult, Safeness};

pub fn check<'tcx>(
    global_env: &GlobalEnv<'tcx>,
    body: &Body<'tcx>,
    fn_sig: &core::FnSig,
) -> Result<(), ErrorReported> {
    let bb_envs = Checker::infer(global_env, body, fn_sig)?;
    let constraint = Checker::check(global_env, body, fn_sig, bb_envs)?;

    let constraint = constraint.into_fixpoint();
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
        Err(err) => panic!("cannot run fixpoint: {:?}", err),
    }
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
