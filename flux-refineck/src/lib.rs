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
extern crate rustc_target;

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
use flux_macros::fluent_messages;
use flux_middle::{global_env::GlobalEnv, rty, rustc::mir::Body};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use rustc_hir::def_id::DefId;

fluent_messages! { "../locales/en-US.ftl" }

pub fn check_fn<'tcx>(
    genv: &GlobalEnv<'_, 'tcx>,
    cache: &mut QueryCache,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Result<(), ErrorGuaranteed> {
    dbg::check_fn_span!(genv.tcx, def_id).in_scope(|| {
        // PHASE 1: infer shape of basic blocks
        let shape_result = Checker::run_in_shape_mode(genv, body, def_id).emit(genv.sess)?;
        tracing::info!("Checker::shape");

        // PHASE 2: generate refinement tree constraint
        let (mut refine_tree, kvars) =
            Checker::run_in_refine_mode(genv, body, def_id, shape_result).emit(genv.sess)?;
        tracing::info!("Checker::refine");

        // PHASE 3: invoke fixpoint on the constraints
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
        tracing::info!("Fixpoint::check");

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
    #[diag(refineck_goto_error, code = "FLUX")]
    pub struct GotoError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_call_error, code = "FLUX")]
    pub struct CallError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_assign_error, code = "FLUX")]
    pub struct AssignError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_ret_error, code = "FLUX")]
    pub struct RetError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_div_error, code = "FLUX")]
    pub struct DivError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_rem_error, code = "FLUX")]
    pub struct RemError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_assert_error, code = "FLUX")]
    pub struct AssertError {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_fold_error, code = "FLUX")]
    pub struct FoldError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_overflow_error, code = "FLUX")]
    pub struct OverflowError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_unknown_error, code = "FLUX")]
    pub struct UnknownError {
        #[primary_span]
        pub span: Span,
    }
}
