#![feature(
    rustc_private,
    min_specialization,
    once_cell,
    generic_associated_types,
    if_let_guard,
    let_chains
)]

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
mod constraint_gen;
mod dbg;
mod param_infer;
mod refine_tree;
mod type_env;
pub mod wf;

mod fixpoint;

use std::{fs, io::Write};

use checker::Checker;
use constraint_gen::Tag;
use liquid_rust_common::config::CONFIG;
use liquid_rust_middle::{global_env::GlobalEnv, rustc::mir::Body, ty};
use rustc_errors::ErrorReported;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub fn check<'tcx>(
    genv: &GlobalEnv<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
    qualifiers: &[ty::Qualifier],
) -> Result<(), ErrorReported> {
    let bb_envs = Checker::infer(genv, body, def_id)?;
    let mut kvars = fixpoint::KVarStore::new();
    let refine_tree = Checker::check(genv, body, def_id, &mut kvars, bb_envs)?;

    if CONFIG.dump_constraint {
        dump_constraint(genv.tcx, def_id, &refine_tree, ".lrc").unwrap();
    }

    let mut fcx = fixpoint::FixpointCtxt::new(kvars);

    let constraint = refine_tree.into_fixpoint(&mut fcx);

    match fcx.check(genv.tcx, def_id, constraint, qualifiers) {
        Ok(_) => Ok(()),
        Err(tags) => report_errors(genv.tcx, body.span(), tags),
    }
}

fn report_errors(tcx: TyCtxt, body_span: Span, errors: Vec<Tag>) -> Result<(), ErrorReported> {
    for err in errors {
        match err {
            Tag::Call(span) => tcx.sess.emit_err(errors::CallError { span }),
            Tag::Assign(span) => tcx.sess.emit_err(errors::AssignError { span }),
            Tag::Ret => tcx.sess.emit_err(errors::RetError { span: body_span }),
            Tag::Div(span) => tcx.sess.emit_err(errors::DivError { span }),
            Tag::Rem(span) => tcx.sess.emit_err(errors::RemError { span }),
            Tag::Goto(span, bb) => tcx.sess.emit_err(errors::GotoError { span, bb }),
            Tag::Assert(msg, span) => tcx.sess.emit_err(errors::AssertError { msg, span }),
        };
    }

    Err(ErrorReported)
}

/// TODO(nilehmann) we should abstract over dumping files logic
fn dump_constraint<C: std::fmt::Debug>(
    tcx: TyCtxt,
    def_id: DefId,
    c: &C,
    suffix: &str,
) -> Result<(), std::io::Error> {
    let dir = CONFIG.log_dir.join("horn");
    fs::create_dir_all(&dir)?;
    let mut file = fs::File::create(dir.join(format!("{}{}", tcx.def_path_str(def_id), suffix)))?;
    write!(file, "{:?}", c)
}

mod errors {
    use liquid_rust_middle::rustc::mir::BasicBlock;
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct GotoError {
        #[message = "error jumping to join point: `{bb:?}`"]
        pub span: Option<Span>,
        pub bb: BasicBlock,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct CallError {
        #[message = "precondition might not hold"]
        #[label = "precondition might not hold in this function call"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct AssignError {
        #[message = "missmatched type in assignment"]
        #[label = "this assignment might be unsafe"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RetError {
        #[message = "postcondition might not hold"]
        #[label = "the postcondition in this function might not hold"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DivError {
        #[message = "possible division by zero"]
        #[label = "denominator might be zero"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RemError {
        #[message = "possible reminder with a divisor of zero"]
        #[label = "divisor might not be zero"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct AssertError {
        #[message = "assertion might fail: {msg}"]
        pub span: Span,
        pub msg: &'static str,
    }
}
