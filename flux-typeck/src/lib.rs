#![feature(rustc_private, min_specialization, once_cell, if_let_guard)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
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
use flux_common::config::CONFIG;
use flux_middle::{global_env::GlobalEnv, rustc::mir::Body, ty};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub fn check<'a, 'tcx>(
    genv: &GlobalEnv<'a, 'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
    qualifiers: &[ty::Qualifier],
) -> Result<(), ErrorGuaranteed> {
    let bb_envs = Checker::infer(genv, body, def_id)?;
    let mut kvars = fixpoint::KVarStore::new();
    let refine_tree = Checker::check(genv, body, def_id, &mut kvars, bb_envs)?;

    if CONFIG.dump_constraint {
        dump_constraint(genv.tcx, def_id, &refine_tree, ".lrc").unwrap();
    }

    let mut fcx = fixpoint::FixpointCtxt::new(&genv.consts, kvars);

    let constraint = refine_tree.into_fixpoint(&mut fcx);

    match fcx.check(genv.tcx, def_id, constraint, qualifiers, &genv.uf_sorts) {
        Ok(_) => Ok(()),
        Err(tags) => report_errors(genv, body.span(), tags),
    }
}

fn report_errors(
    genv: &GlobalEnv,
    body_span: Span,
    errors: Vec<Tag>,
) -> Result<(), ErrorGuaranteed> {
    let mut e = None;
    for err in errors {
        e = Some(match err {
            Tag::Call(span) => genv.sess.emit_err(errors::CallError { span }),
            Tag::Assign(span) => genv.sess.emit_err(errors::AssignError { span }),
            Tag::Ret => genv.sess.emit_err(errors::RetError { span: body_span }),
            Tag::RetAt(span) => genv.sess.emit_err(errors::RetError { span }),
            Tag::Div(span) => genv.sess.emit_err(errors::DivError { span }),
            Tag::Rem(span) => genv.sess.emit_err(errors::RemError { span }),
            Tag::Goto(span, _) => genv.sess.emit_err(errors::GotoError { span }),
            Tag::Assert(msg, span) => genv.sess.emit_err(errors::AssertError { span, msg }),
            Tag::Fold(span) => genv.sess.emit_err(errors::FoldError { span }),
            Tag::Other => genv.sess.emit_err(errors::UnknownError { span: body_span }),
        });
    }

    if let Some(e) = e {
        Err(e)
    } else {
        Ok(())
    }
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
    use flux_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error(refineck::goto_error, code = "FLUX")]
    pub struct GotoError {
        #[primary_span]
        pub span: Option<Span>,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::call_error, code = "FLUX")]
    pub struct CallError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::assign_error, code = "FLUX")]
    pub struct AssignError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::ret_error, code = "FLUX")]
    pub struct RetError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::div_error, code = "FLUX")]
    pub struct DivError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::rem_error, code = "FLUX")]
    pub struct RemError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::assert_error, code = "FLUX")]
    pub struct AssertError {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::fold_error, code = "FLUX")]
    pub struct FoldError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(refineck::unknown_error, code = "FLUX")]
    pub struct UnknownError {
        #[primary_span]
        pub span: Span,
    }
}
