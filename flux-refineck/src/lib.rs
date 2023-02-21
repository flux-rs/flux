#![feature(
    rustc_private,
    min_specialization,
    once_cell,
    if_let_guard,
    let_chains,
    type_alias_impl_trait,
    box_patterns,
    drain_filter,
    result_option_inspect
)]
///! Refinement type checking
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
pub mod invariants;
mod param_infer;
mod refine_tree;
mod type_env;
pub mod wf;

mod fixpoint;
mod sigs;

use checker::Checker;
use constraint_gen::{ConstrReason, Tag};
use flux_common::{cache::QueryCache, dbg};
use flux_config as config;
use flux_errors::ResultExt;
use flux_middle::{global_env::GlobalEnv, rty, rustc::mir::Body};
use itertools::Itertools;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;

use crate::refine_tree::RefineTree;

pub fn check_fn<'tcx>(
    genv: &GlobalEnv<'_, 'tcx>,
    cache: &mut QueryCache,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Result<(), ErrorGuaranteed> {
    dbg::check_fn_span!(genv.tcx, def_id).in_scope(|| {
        let bb_envs = Checker::infer(genv, body, def_id).emit(genv.sess)?;

        tracing::info!("Checker::infer");

        let mut kvars = fixpoint::KVarStore::new();
        let mut refine_tree = RefineTree::new();
        Checker::check(genv, body, def_id, refine_tree.as_subtree(), &mut kvars, bb_envs)
            .emit(genv.sess)?;

        tracing::info!("Checker::check");

        refine_tree.simplify();

        if config::dump_constraint() {
            dbg::dump_item_info(genv.tcx, def_id, "fluxc", &refine_tree).unwrap();
        }

        let mut fcx = fixpoint::FixpointCtxt::new(genv, def_id, kvars);

        let constraint = refine_tree.into_fixpoint(&mut fcx);

        let result = match fcx.check(cache, constraint) {
            Ok(_) => Ok(()),
            Err(tags) => report_errors(genv, tags),
        };

        tracing::info!("FixpointCtx::check");

        result
    })
}

fn report_errors(genv: &GlobalEnv, errors: Vec<Tag>) -> Result<(), ErrorGuaranteed> {
    let mut e = None;
    for err in errors {
        let span = err.span;
        e = Some(match err.reason {
            ConstrReason::Call => genv.sess.emit_err(errors::CallError { span }),
            ConstrReason::Assign => genv.sess.emit_err(errors::AssignError { span }),
            ConstrReason::Ret => genv.sess.emit_err(errors::RetError { span }),
            ConstrReason::Div => genv.sess.emit_err(errors::DivError { span }),
            ConstrReason::Rem => genv.sess.emit_err(errors::RemError { span }),
            ConstrReason::Goto(_) => genv.sess.emit_err(errors::GotoError { span }),
            ConstrReason::Assert(msg) => genv.sess.emit_err(errors::AssertError { span, msg }),
            ConstrReason::Fold => genv.sess.emit_err(errors::FoldError { span }),
            ConstrReason::Overflow => genv.sess.emit_err(errors::OverflowError { span }),
            ConstrReason::Other => genv.sess.emit_err(errors::UnknownError { span }),
        });
    }

    if let Some(e) = e {
        Err(e)
    } else {
        Ok(())
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(refineck::goto_error, code = "FLUX")]
    pub struct GotoError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::call_error, code = "FLUX")]
    pub struct CallError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::assign_error, code = "FLUX")]
    pub struct AssignError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::ret_error, code = "FLUX")]
    pub struct RetError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::div_error, code = "FLUX")]
    pub struct DivError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::rem_error, code = "FLUX")]
    pub struct RemError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::assert_error, code = "FLUX")]
    pub struct AssertError {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::fold_error, code = "FLUX")]
    pub struct FoldError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::overflow_error, code = "FLUX")]
    pub struct OverflowError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck::unknown_error, code = "FLUX")]
    pub struct UnknownError {
        #[primary_span]
        pub span: Span,
    }
}
