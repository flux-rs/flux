//! Refinement type checking

#![feature(
    associated_type_defaults,
    box_patterns,
    extract_if,
    if_let_guard,
    let_chains,
    min_specialization,
    never_type,
    rustc_private,
    unwrap_infallible
)]

extern crate rustc_data_structures;
extern crate rustc_errors;

extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

mod checker;
pub mod compare_impl_item;
mod ghost_statements;
pub mod invariants;
mod primops;
mod queue;
mod type_env;

use std::collections::{HashMap, HashSet};

use checker::{Checker, trait_impl_subtyping};
use flux_common::{dbg, result::ResultExt as _};
use flux_infer::{
    fixpoint_encoding::{FixQueryCache, FixpointCheckError},
    infer::{ConstrReason, SubtypeReason, Tag},
    refine_tree::{BinderDeps, BinderOriginator, BinderProvenance, CallReturn},
};
use flux_macros::fluent_messages;
use flux_middle::{
    FixpointQueryKind,
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    pretty,
    rty::{self, ESpan, Name, fold::TypeVisitable},
    timings
};
use itertools::Itertools;
use rustc_errors::{Diag, ErrorGuaranteed};
use rustc_hir::def_id::LocalDefId;
use rustc_span::Span;

use crate::{checker::errors::ResultExt as _, ghost_statements::compute_ghost_statements};

fluent_messages! { "../locales/en-US.ftl" }

fn report_fixpoint_errors(
    genv: GlobalEnv,
    local_id: LocalDefId,
    errors: Vec<FixpointCheckError<Tag>>,
) -> Result<(), ErrorGuaranteed> {
    #[expect(clippy::collapsible_else_if, reason = "it looks better")]
    if genv.should_fail(local_id) {
        if errors.is_empty() { report_expected_neg(genv, local_id) } else { Ok(()) }
    } else {
        if errors.is_empty() { Ok(()) } else { report_errors(genv, errors) }
    }
}

pub fn check_fn(
    genv: GlobalEnv,
    cache: &mut FixQueryCache,
    def_id: LocalDefId,
) -> Result<(), ErrorGuaranteed> {
    let span = genv.tcx().def_span(def_id);

    // HACK(nilehmann) this will ignore any code generated by a macro. This is a temporary
    // workaround to deal with a `#[derive(..)]` that generates code that flux cannot handle.
    // Note that this is required because code generated by a `#[derive(..)]` cannot be
    // manually trusted or ignored.
    if !genv.tcx().def_span(def_id).ctxt().is_root() {
        return Ok(());
    }

    // Skip trait methods without body
    if genv.tcx().hir_node_by_def_id(def_id).body_id().is_none() {
        return Ok(());
    }

    let opts = genv.infer_opts(def_id);

    // FIXME(nilehmann) we should move this check to `compare_impl_item`
    if let Some(infcx_root) = trait_impl_subtyping(genv, def_id, opts, span)
        .with_span(span)
        .map_err(|err| err.emit(genv, def_id))?
    {
        tracing::info!("check_fn::refine-subtyping");
        let errors = infcx_root
            .execute_fixpoint_query(cache, MaybeExternId::Local(def_id), FixpointQueryKind::Impl)
            .emit(&genv)?;
        tracing::info!("check_fn::fixpoint-subtyping");
        report_fixpoint_errors(genv, def_id, errors)?;
    }

    // Skip trusted functions
    if genv.trusted(def_id) {
        return Ok(());
    }

    timings::time_it(timings::TimingKind::CheckFn(def_id), || -> Result<(), ErrorGuaranteed> {
        let ghost_stmts = compute_ghost_statements(genv, def_id)
            .with_span(span)
            .map_err(|err| err.emit(genv, def_id))?;

        // PHASE 1: infer shape of `TypeEnv` at the entry of join points
        let shape_result = Checker::run_in_shape_mode(genv, def_id, &ghost_stmts, opts)
            .map_err(|err| err.emit(genv, def_id))?;

        // PHASE 2: generate refinement tree constraint
        let infcx_root =
            Checker::run_in_refine_mode(genv, def_id, &ghost_stmts, shape_result, opts)
                .map_err(|err| err.emit(genv, def_id))?;

        // PHASE 3: invoke fixpoint on the constraint
        let errors = infcx_root
            .execute_fixpoint_query(cache, MaybeExternId::Local(def_id), FixpointQueryKind::Body)
            .emit(&genv)?;
        report_fixpoint_errors(genv, def_id, errors)
    })?;

    dbg::check_fn_span!(genv.tcx(), def_id).in_scope(|| Ok(()))
}

fn call_error<'a>(genv: GlobalEnv<'a, '_>, span: Span, dst_span: Option<ESpan>) -> Diag<'a> {
    genv.sess()
        .dcx()
        .handle()
        .create_err(errors::RefineError::call(span, dst_span))
}

fn ret_error<'a>(genv: GlobalEnv<'a, '_>, span: Span, dst_span: Option<ESpan>) -> Diag<'a> {
    genv.sess()
        .dcx()
        .handle()
        .create_err(errors::RefineError::ret(span, dst_span))
}

fn report_errors(
    genv: GlobalEnv,
    errors: Vec<FixpointCheckError<Tag>>,
) -> Result<(), ErrorGuaranteed> {
    let mut e = None;
    for err in errors {
        let span = err.tag.src_span;
        let mut err_diag = match err.tag.reason {
            ConstrReason::Call
            | ConstrReason::Subtype(SubtypeReason::Input)
            | ConstrReason::Subtype(SubtypeReason::Requires) => {
                call_error(genv, span, err.tag.dst_span)
            }
            ConstrReason::Assign => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::AssignError { span })
            }
            ConstrReason::Ret
            | ConstrReason::Subtype(SubtypeReason::Output)
            | ConstrReason::Subtype(SubtypeReason::Ensures) => {
                ret_error(genv, span, err.tag.dst_span)
            }
            ConstrReason::Div => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::DivError { span })
            }
            ConstrReason::Rem => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::RemError { span })
            }
            ConstrReason::Goto(_) => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::GotoError { span })
            }
            ConstrReason::Assert(msg) => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::AssertError { span, msg })
            }
            ConstrReason::Fold | ConstrReason::FoldLocal => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::FoldError { span })
            }
            ConstrReason::Overflow => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::OverflowError { span })
            }
            ConstrReason::Other => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::UnknownError { span })
            }
        };

        let (mut binders, subst) =
            binders_and_subst_from_expr(genv, &err.blame_spans.expr, &err.blame_spans.binder_deps);
        let pred_pretty_cx = pretty::PrettyCx::default(genv).with_free_var_substs(subst);
        err_diag.subdiagnostic(errors::FailingConstraint {
            constraint: format!("{:?}", pretty::with_cx!(&pred_pretty_cx, &err.blame_spans.expr)),
        });
        if let Some(first_binder) = binders.pop() {
            add_blame_var_diagnostic(genv, &mut err_diag, first_binder);
        }
        for binder in binders.into_iter().rev() {
            add_related_var_diagnostic(genv, &mut err_diag, binder);
        }

        e = Some(err_diag.emit());

        // 1. [ ] Create a subdiagnostic for the provenance of a variable (could just modify BlameSpan)
        // 2. [ ] Create a subdiagnostic for the variable we are suggesting to fix.
        // 3. [ ] Create specialized subdiagnostics for the above for the different CallReturn and FnArg cases.
        // 4. [x] Make a struct for the blame_spans field and in addition to everything being tracked
        //        currently, also track a list of just the binders in the failing constraint (this is just expr.fvars()).
        // 5. [ ] Write a heuristic function to pick a singular blame variable from the binders.
        //        (for now, we can probably just pick the deepest one which is related to all of
        //         the vars in the constraint)
        // 6. [ ] Emit the friendly constraint as a note beneath the initial error.
        // 7. [ ] Emit the suggested var to change next.
        // 8. [ ] Emit the subdiagnostics identifying the variables in the constraint after (and only the variables in the constraint).
        // let vars_and_originators: String = err.blame_spans.0.iter()
        //                                                   .map(|(name, bp, depth)| {
        //                                                       let origin_str = match bp {
        //                                                           Some(bp@BinderProvenance {originator: origin, span}) => {
        //                                                               add_substitution_for_binder_var(genv, &mut pred_pretty_cx.free_var_substs, *name, bp);
        //                                                               format!("({:?}, {:?})", origin, span)
        //                                                           },
        //                                                           _ => "No provenance".to_string(),
        //                                                       };
        //                                                       format!(r#"{{"name": "{:?}", "pretty_name": "{:?}", "depth": {}, "origin": {:?}}}"#,
        //                                                               name,
        //                                                               pred_pretty_cx.free_var_substs.get(&name),
        //                                                               depth,
        //                                                               origin_str)
        //                                                   }).join(", ");
        // // We populate the PrettyCx.free_var_substs so that when we pretty print
        // // the failing predicate, we give better names to the failing variables.
        // let pred_string = format!(r#""{:?}""#, pretty::with_cx!(&pred_pretty_cx, err.blame_spans.1));
        // let blame_span_err = errors::ErrWithBlameSpans {
        //     span,
        //     // For now, swallow blame spans without emitting any errors
        //     blame_spans: err
        //         .blame_spans
        //         .0
        //         .iter()
        //         .filter_map(|(name, bp, _depth)| {
        //             bp.clone().and_then(|bp| {
        //                 bp.span.map(|span| {
        //                     errors::BlameSpan {
        //                         // Use the substituted name if it exists
        //                         var: if let Some(subst) = pred_pretty_cx.free_var_substs.get(&name) {
        //                                 format!("{}", subst)
        //                              } else {
        //                                 format!("{:?}", name)
        //                              },
        //                         span,
        //                         originator: format!("{:?}", bp.originator),
        //                     }
        //                 })
        //             })
        //         })
        //         .collect(),
        //     // Omit span information in this debug print
        //     related_vars: format!("[{}]", vars_and_originators),
        //     blame_var: format!(r#""{:?}""#, err.blame_spans.2),
        //     pred: pred_string,
        // };
        // genv.sess().emit_err(blame_span_err);
    }

    if let Some(e) = e { Err(e) } else { Ok(()) }
}

fn report_expected_neg(genv: GlobalEnv, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
    Err(genv.sess().emit_err(errors::ExpectedNeg {
        span: genv.tcx().def_span(def_id),
        def_descr: genv.tcx().def_descr(def_id.to_def_id()),
    }))
}

// Returns whether we found a substitution for the var
fn add_substitution_for_binder_var(
    genv: GlobalEnv,
    subst: &mut HashMap<Name, String>,
    var_name: Name,
    binder_provenance: &BinderProvenance,
) -> bool {
    match binder_provenance.originator {
        BinderOriginator::FnArg(Some(arg_name)) => {
            subst.insert(var_name, arg_name.to_string());
            return true;
        }
        BinderOriginator::CallReturn(CallReturn { destination_name, .. }) => {
            // First priority: use the name that the function call is bound to, e.g. if we write
            //
            // let x = foo()
            //
            // we will use `x` as the name for binder var for `foo()`
            // (this doesn't handle shadowing or mutation)
            if let Some(destination_name) = destination_name {
                subst.insert(var_name, destination_name.to_string());
                return true;
            // Second priority: use the function call itself if it fits on a
            // single line, e.g. if we have
            //
            // return foo()
            //
            // we will use `foo()` as the name for the binder var for `foo()`.
            } else if let Some(span) = binder_provenance.span {
                let source_snippet = genv.tcx().sess.source_map().span_to_snippet(span);
                if let Ok(source_snippet) = source_snippet
                    && !source_snippet.contains("\n")
                {
                    subst.insert(var_name, source_snippet);
                    return true;
                }
            }
            // Otherwise: we will not rename the var.
            //
            // It may be that we do not have a span for it or that it spans
            // multiple lines.
        }
        _ => {}
    }
    false
}

// Extract information on all of the binders in the expression (1st part of output)
// as well as a substitution from the binder names to better names (2nd part of output)
//
// We also sort the binders because we'll suggest fixing the first binder.
// Sorting is done with the best given last.
// Right now the heuristic for ordering binders is just to prefer the one defined
// latest, but it will be improved eventually.
fn binders_and_subst_from_expr(
    genv: GlobalEnv,
    expr: &rty::Expr,
    binder_deps: &BinderDeps,
) -> (Vec<BinderInfo>, HashMap<Name, String>) {
    let mut subst = HashMap::new();
    let mut binders: Vec<BinderInfo> = expr
        .fvars()
        .iter()
        .filter_map(|name| {
            // We can only report information for variables which
            // 1. We have information for (this should be all variables...)
            binder_deps
                .get(name)
                .and_then(|(bp_opt, depth, related_vars)| {
                    // 2. Have a provenance.
                    bp_opt.as_ref().and_then(|bp| {
                        // Collect the subst info.
                        add_substitution_for_binder_var(genv, &mut subst, *name, bp);
                        // 3. Have a span
                        bp.span.map(|span| {
                            BinderInfo {
                                name: *name,
                                pretty_name: subst.get(name).cloned(),
                                span,
                                originator: bp.originator.clone(),
                                depth: *depth,
                                related_vars: related_vars.clone(),
                            }
                        })
                    })
                })
        })
        .collect();
    binders.sort_by_key(|bi| bi.depth);
    (binders, subst)
}

fn add_blame_var_diagnostic<'a>(
    genv: GlobalEnv<'a, '_>,
    diag: &mut Diag<'a>,
    binder_info: BinderInfo,
) {
    match binder_info.originator {
        // If our blamed variable comes from a function return, suggest modifying
        // the function instead of the variable.
        BinderOriginator::CallReturn(CallReturn { def_id: Some(def_id), .. }) => {
            let fn_name = genv.tcx().def_path_str(def_id);
            let fn_span = genv
                .tcx()
                .def_ident_span(def_id)
                .unwrap_or_else(|| genv.tcx().def_span(def_id));
            diag.subdiagnostic(errors::BlamedFn { span: fn_span, fn_name });
            // Show where the var is defined too.
            add_var_span_diagnostic(diag, binder_info);
        }
        // As a fallback, suggest modifying the variable.
        _ => {
            diag.subdiagnostic(errors::BlamedVar {
                span: binder_info.span,
                var: binder_info
                    .pretty_name
                    .unwrap_or(format!("{:?}", binder_info.name)),
            });
        }
    }
}

// Don't use this at a top level, it's code meant to be shared between add_blame_var and add_related_var
fn add_var_span_diagnostic(diag: &mut Diag<'_>, binder_info: BinderInfo) {
    diag.subdiagnostic(errors::VarSpan {
        span: binder_info.span,
        var: binder_info
            .pretty_name
            .unwrap_or(format!("{:?}", binder_info.name)),
    });
}

fn add_related_var_diagnostic<'a>(
    genv: GlobalEnv<'a, '_>,
    diag: &mut Diag<'a>,
    binder_info: BinderInfo,
) {
    diag.subdiagnostic(errors::VarSpan {
        span: binder_info.span,
        var: binder_info
            .pretty_name
            .unwrap_or(format!("{:?}", binder_info.name)),
    });
    if let BinderOriginator::CallReturn(CallReturn { def_id: Some(def_id), .. }) = binder_info.originator {
        let fn_name = genv.tcx().def_path_str(def_id);
        let fn_span = genv
            .tcx()
            .def_ident_span(def_id)
            .unwrap_or_else(|| genv.tcx().def_span(def_id));
        diag.subdiagnostic(errors::RelatedFn { span: fn_span, fn_name });
    }
}

#[derive(Debug, Clone)]
struct BinderInfo {
    name: Name,
    pretty_name: Option<String>,
    span: Span,
    originator: BinderOriginator,
    depth: usize,
    related_vars: HashSet<Name>,
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::{Diagnostic, Subdiagnostic};
    use flux_middle::rty::ESpan;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(refineck_goto_error, code = E0999)]
    pub struct GotoError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_assign_error, code = E0999)]
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
    #[diag(refineck_refine_error, code = E0999)]
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
                    let span_note = Some(ConditionSpanNote { span: dst_span.span });
                    let call_span_note = dst_span.base.map(|span| CallSpanNote { span });
                    RefineError { span, cond, span_note, call_span_note }
                }
                None => RefineError { span, cond, span_note: None, call_span_note: None },
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(refineck_div_error, code = E0999)]
    pub struct DivError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_rem_error, code = E0999)]
    pub struct RemError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_assert_error, code = E0999)]
    pub struct AssertError {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_fold_error, code = E0999)]
    pub struct FoldError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_overflow_error, code = E0999)]
    pub struct OverflowError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_unknown_error, code = E0999)]
    pub struct UnknownError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(refineck_expected_neg, code = E0999)]
    pub struct ExpectedNeg {
        #[primary_span]
        pub span: Span,
        pub def_descr: &'static str,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_failing_constraint_note)]
    pub struct FailingConstraint {
        pub constraint: String,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_blamed_fn_note)]
    pub struct BlamedFn {
        #[primary_span]
        pub span: Span,
        pub fn_name: String,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_blamed_var_note)]
    pub struct BlamedVar {
        #[primary_span]
        pub span: Span,
        pub var: String,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_var_span_note)]
    pub struct VarSpan {
        #[primary_span]
        pub span: Span,
        pub var: String,
        // pub originator: String,
    }

    #[derive(Subdiagnostic)]
    #[note(refineck_var_span_note)]
    pub struct RelatedFn {
        #[primary_span]
        pub span: Span,
        pub fn_name: String,
    }

    // refineck_err_with_blame_spans =
    // failed to verify predicate: {$pred}
    // blamed variable: {$blame_var}
    // related variables: {$related_vars}
    //
    // #[derive(Diagnostic)]
    // #[diag(refineck_err_with_blame_spans, code = E0999)]
    // pub struct ErrWithBlameSpans {
    //     #[primary_span]
    //     pub span: Span,
    //     #[subdiagnostic]
    //     pub blame_spans: Vec<BlameSpan>,
    //     pub related_vars: String,
    //     pub pred: String,
    //     pub blame_var: String,
    // }
}
