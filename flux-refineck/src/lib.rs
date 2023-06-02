//! Refinement type checking

#![warn(unused_extern_crates)]
#![feature(
    box_patterns,
    drain_filter,
    if_let_guard,
    impl_trait_in_assoc_type,
    lazy_cell,
    let_chains,
    min_specialization,
    never_type,
    result_option_inspect,
    rustc_private,
    type_alias_impl_trait
)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_type_ir;

mod checker;
mod constraint_gen;
mod fixpoint_encoding;
pub mod invariants;
mod param_infer;
mod place_analysis;
mod queue;
mod refine_tree;
mod sigs;
mod type_env;

use checker::Checker;
pub use checker::CheckerConfig;
use constraint_gen::{ConstrReason, Tag};
use flux_common::{cache::QueryCache, dbg};
use flux_config as config;
use flux_errors::ResultExt;
use flux_macros::fluent_messages;
use flux_middle::{
    global_env::GlobalEnv,
    rty::{self, ESpan},
};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use rustc_hir::def_id::LocalDefId;
use rustc_span::Span;

fluent_messages! { "../locales/en-US.ftl" }

pub fn check_fn(
    genv: &GlobalEnv,
    cache: &mut QueryCache,
    local_id: LocalDefId,
    config: CheckerConfig,
) -> Result<(), ErrorGuaranteed> {
    let def_id = local_id.to_def_id();
    dbg::check_fn_span!(genv.tcx, def_id).in_scope(|| {
        if genv.map().is_trusted(local_id) {
            return Ok(());
        }
        // HACK(nilehmann) this will ignore any code generated by a macro. This is
        // a temporary workaround to allow `#[derive(PartialEq, Eq)]` and should be
        // removed.
        if genv.tcx.def_span(def_id).ctxt() > rustc_span::SyntaxContext::root() {
            return Ok(());
        }

        // PHASE 1: infer shape of `TypeEnv` at the entry of join points
        let shape_result = Checker::run_in_shape_mode(genv, def_id, config).emit(genv.sess)?;
        tracing::info!("check_fn::shape");

        // PHASE 2: generate refinement tree constraint
        let (mut refine_tree, kvars) =
            Checker::run_in_refine_mode(genv, def_id, shape_result, config).emit(genv.sess)?;
        tracing::info!("check_fn::refine");

        // PHASE 3: invoke fixpoint on the constraint
        refine_tree.simplify();
        if config::dump_constraint() {
            dbg::dump_item_info(genv.tcx, def_id, "fluxc", &refine_tree).unwrap();
        }
        let mut fcx = fixpoint_encoding::FixpointCtxt::new(genv, def_id, kvars);
        let constraint = refine_tree.into_fixpoint(&mut fcx);
        let errors = fcx.check(cache, constraint, &config).emit(genv.sess)?;

        tracing::info!("check_fn::fixpoint");
        if errors.is_empty() {
            Ok(())
        } else {
            report_errors(genv, errors)
        }
    })
}

fn call_error(genv: &GlobalEnv, span: Span, dst_span: Option<ESpan>) -> ErrorGuaranteed {
    genv.sess
        .emit_err(errors::RefineError::call(span, dst_span))
}

fn ret_error(genv: &GlobalEnv, span: Span, dst_span: Option<ESpan>) -> ErrorGuaranteed {
    genv.sess.emit_err(errors::RefineError::ret(span, dst_span))
}

fn report_errors(genv: &GlobalEnv, errors: Vec<Tag>) -> Result<(), ErrorGuaranteed> {
    let mut e = None;
    for err in errors {
        let span = err.src_span;
        e = Some(match err.reason {
            ConstrReason::Call => call_error(genv, span, err.dst_span),
            ConstrReason::Assign => genv.sess.emit_err(errors::AssignError { span }),
            ConstrReason::Ret => ret_error(genv, span, err.dst_span),
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
    use flux_macros::{Diagnostic, Subdiagnostic};
    use flux_middle::rty::ESpan;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(refineck_goto_error, code = "FLUX")]
    pub struct GotoError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_assign_error, code = "FLUX")]
    pub struct AssignError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_condition_span_note)]
    pub(crate) struct ConditionSpanNote {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_call_span_note)]
    pub(crate) struct CallSpanNote {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_refine_error, code = "FLUX")]
    pub struct RefineError {
        #[primary_span]
        #[label]
        pub span: Span,
        cond: &'static str,
        #[subdiagnostic]
        span_note: Option<ConditionSpanNote>,
        #[subdiagnostic]
        call_span_note: Option<CallSpanNote>,
    }

    impl RefineError {
        pub fn call(span: Span, espan: Option<ESpan>) -> Self {
            RefineError::new("precondition", span, espan)
        }

        pub fn ret(span: Span, espan: Option<ESpan>) -> Self {
            RefineError::new("postcondition", span, espan)
        }

        fn new(cond: &'static str, span: Span, espan: Option<ESpan>) -> RefineError {
            match espan {
                Some(dst_span) => {
                    let span_note = Some(ConditionSpanNote { span: dst_span.span() });
                    let call_span_note = dst_span.base().map(|span| CallSpanNote { span });
                    RefineError { span, cond, span_note, call_span_note }
                }
                None => RefineError { span, cond, span_note: None, call_span_note: None },
            }
        }
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
