//! Refinement type checking

#![feature(
    associated_type_defaults,
    deref_patterns,
    min_specialization,
    rustc_private,
    unwrap_infallible
)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_type_ir;

mod checker;
pub mod compare_impl_item;
pub mod fixpoint;
mod ghost_statements;
pub mod invariants;
mod primops;
mod queue;
mod type_env;

use checker::{Checker, trait_impl_subtyping};
use flux_common::{dbg, dbg::SpanTrace, result::ResultExt as _};
use flux_config as config;
use flux_infer::{
    fixpoint_encoding::{
        FixQueryCache, FixpointCheckError, PossibleSolutions, SolutionTrace, TagIdx,
    },
    infer::{ConstrReason, SubtypeReason, Tag},
    wkvars::WKVarSubst,
};
use flux_macros::msg;
use flux_middle::{
    FixpointQueryKind,
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    metrics::{self, Metric, TimingKind},
    pretty,
    rty::{self, ESpan, EarlyBinder, fold::TypeFoldable},
};
use rustc_data_structures::{
    fx::{FxHashMap, FxHashSet},
    unord::UnordMap,
};
use rustc_errors::{Applicability, Diag, ErrorGuaranteed};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_span::Span;

use crate::{checker::errors::ResultExt as _, ghost_statements::compute_ghost_statements};

pub fn report_fixpoint_errors(
    genv: GlobalEnv,
    local_id: LocalDefId,
    errors: Vec<FixpointCheckError<Tag>>,
) -> Result<(), ErrorGuaranteed> {
    #[expect(clippy::collapsible_else_if, reason = "it looks better")]
    if genv.should_fail(local_id) {
        if errors.is_empty() { report_expected_neg(genv, local_id) } else { Ok(()) }
    } else {
        if errors.is_empty() { Ok(()) } else { report_errors(genv, local_id, errors) }
    }
}

pub(crate) fn report_fixpoint_queries(
    genv: GlobalEnv,
    local_id: LocalDefId,
    query_errors: Vec<Vec<FixpointCheckError<Tag>>>,
    query_failed: bool,
    fixes: &UnordMap<rty::WKVid, rty::Binder<rty::Expr>>,
    emitted_fixes: &mut FxHashSet<DefId>,
) -> Result<(), ErrorGuaranteed> {
    let has_errors = query_errors.iter().any(|errors| !errors.is_empty());
    if genv.should_fail(local_id) {
        if has_errors {
            let result = report_fixpoint_errors(
                genv,
                local_id,
                query_errors.into_iter().flatten().collect(),
            );
            if !fixes.is_empty() && emitted_fixes.insert(local_id.to_def_id()) {
                report_standalone_fn_fix(genv, local_id.to_def_id(), fixes);
            }
            return result;
        }
        if query_failed {
            if !fixes.is_empty() && emitted_fixes.insert(local_id.to_def_id()) {
                report_standalone_fn_fix(genv, local_id.to_def_id(), fixes);
            }
            return Ok(());
        }
        let mut diag = genv.sess().dcx().create_err(errors::ExpectedNeg {
            span: genv.tcx().def_span(local_id),
            def_descr: genv.tcx().def_descr(local_id.to_def_id()),
        });
        if !fixes.is_empty() {
            add_fn_fix_diagnostic(genv, &mut diag, local_id.to_def_id(), fixes);
            emitted_fixes.insert(local_id.to_def_id());
        }
        return Err(diag.emit_err());
    }
    if !has_errors {
        if !fixes.is_empty() && emitted_fixes.insert(local_id.to_def_id()) {
            report_standalone_fn_fix(genv, local_id.to_def_id(), fixes);
        }
        return Ok(());
    }
    let mut err = None;
    for errors in query_errors.into_iter().filter(|errors| !errors.is_empty()) {
        if let Err(error) =
            report_errors_with_fixes(genv, local_id, errors, Some(fixes), emitted_fixes)
        {
            err = Some(error);
        }
    }
    err.map_or(Ok(()), Err)
}

fn check_body<'genv, 'tcx>(
    genv: GlobalEnv<'genv, 'tcx>,
    cache: &mut FixQueryCache,
    def_id: LocalDefId,
    poly_sig: &rty::PolyFnSig,
    mut deferred: Option<&mut Vec<fixpoint::DeferredQuery<'genv, 'tcx>>>,
) -> Result<(), ErrorGuaranteed> {
    let span = genv.tcx().def_span(def_id);
    let opts = genv.infer_opts(def_id);

    dbg::log_verbose!("FLUX checking: {def_id:?} {span:?}");

    let ghost_stmts = compute_ghost_statements(genv, def_id)
        .with_span(span)
        .map_err(|err| err.emit(genv, def_id))?;
    let mut closures = UnordMap::default();

    // PHASE 1: infer shape of `TypeEnv` at the entry of join points
    let shape_result =
        Checker::run_in_shape_mode(genv, def_id, &ghost_stmts, &mut closures, opts, poly_sig)
            .map_err(|err| err.emit(genv, def_id))?;

    // PHASE 2: generate refinement tree constraint
    let infcx_root = Checker::run_in_refine_mode(
        genv,
        def_id,
        &ghost_stmts,
        &mut closures,
        shape_result,
        opts,
        poly_sig,
    )
    .map_err(|err| err.emit(genv, def_id))?;

    // PHASE 3: invoke fixpoint on the constraint
    if (genv.proven_externally(def_id).is_some() && flux_config::lean().is_check())
        || flux_config::lean().is_emit()
    {
        infcx_root
            .execute_lean_query(cache, MaybeExternId::Local(def_id))
            .emit(&genv)
    } else {
        let answer = if let Some(deferred) = deferred.as_deref_mut() {
            deferred.push(fixpoint::DeferredQuery::body(
                infcx_root
                    .save_fixpoint_query(MaybeExternId::Local(def_id), FixpointQueryKind::Body)
                    .emit(&genv)?,
                def_id,
            ));
            return Ok(());
        } else {
            infcx_root
                .execute_fixpoint_query(
                    cache,
                    MaybeExternId::Local(def_id),
                    FixpointQueryKind::Body,
                )
                .emit(&genv)?
        };

        let tcx = genv.tcx();
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        let body_span = tcx.hir_span_with_body(hir_id);
        dbg::solution!(genv, &answer, body_span);

        let errors = answer.errors;
        report_fixpoint_errors(genv, def_id, errors)
    }
}

pub fn check_static<'genv, 'tcx>(
    genv: GlobalEnv<'genv, 'tcx>,
    cache: &mut FixQueryCache,
    def_id: LocalDefId,
    ty: rty::Ty,
    deferred: Option<&mut Vec<fixpoint::DeferredQuery<'genv, 'tcx>>>,
) -> Result<(), ErrorGuaranteed> {
    // Build a PolyFnSig with no inputs and `ty` as the output
    let output = rty::Binder::dummy(rty::FnOutput::new(ty, vec![]));
    let fn_sig = rty::FnSig::new(
        rustc_hir::Safety::Safe,
        rustc_abi::ExternAbi::Rust,
        rty::List::empty(),
        rty::List::empty(),
        output,
        rty::Expr::ff(),
        false,
    );
    let poly_sig = rty::PolyFnSig::dummy(fn_sig);

    metrics::incr_metric(Metric::FnChecked, 1);
    metrics::time_it(TimingKind::CheckBody(def_id), || {
        check_body(genv, cache, def_id, &poly_sig, deferred)
    })
}

pub fn check_fn<'genv, 'tcx>(
    genv: GlobalEnv<'genv, 'tcx>,
    cache: &mut FixQueryCache,
    def_id: LocalDefId,
    mut deferred: Option<&mut Vec<fixpoint::DeferredQuery<'genv, 'tcx>>>,
) -> Result<(), ErrorGuaranteed> {
    let span = genv.tcx().def_span(def_id);

    // Code generated by a `#[derive(..)]` can't be annotated with `#[trusted]` directly, so a
    // type opts its derived code out of checking with `#[flux::trusted_derive]`. This is needed
    // for types whose derives flux cannot handle, e.g. a `#[flux::opaque]` struct whose derived
    // `Debug`/`Hash` read the internal representation.
    if span.in_derive_expansion()
        && let Some(adt_def_id) = genv.derive_self_ty(def_id)
        && genv.trusted_derive(adt_def_id)
    {
        metrics::incr_metric(Metric::FnTrusted, 1);
        return Ok(());
    }

    let opts = genv.infer_opts(def_id);

    // FIXME(nilehmann) we should move this check to `compare_impl_item`
    if let Some(infcx_root) = trait_impl_subtyping(genv, def_id, opts, span)
        .with_span(span)
        .map_err(|err| err.emit(genv, def_id))?
    {
        tracing::info!("check_fn::refine-subtyping");
        if let Some(deferred) = deferred.as_deref_mut() {
            deferred.push(fixpoint::DeferredQuery::body(
                infcx_root
                    .save_fixpoint_query(MaybeExternId::Local(def_id), FixpointQueryKind::Impl)
                    .emit(&genv)?,
                def_id,
            ));
        } else {
            let answer = infcx_root
                .execute_fixpoint_query(
                    cache,
                    MaybeExternId::Local(def_id),
                    FixpointQueryKind::Impl,
                )
                .emit(&genv)?;
            let errors = answer.errors;
            report_fixpoint_errors(genv, def_id, errors)?;
        }
        tracing::info!("check_fn::fixpoint-subtyping");
    }

    // Skip trusted functions
    if genv.trusted(def_id) {
        metrics::incr_metric(Metric::FnTrusted, 1);
        return Ok(());
    }

    metrics::incr_metric(Metric::FnChecked, 1);
    metrics::time_it(TimingKind::CheckBody(def_id), || -> Result<(), ErrorGuaranteed> {
        let poly_sig = genv
            .fn_sig(def_id)
            .with_span(span)
            .map_err(|err| err.emit(genv, def_id))?
            .instantiate_identity();
        let poly_sig = rty::auto_strong(genv, def_id, poly_sig);

        check_body(genv, cache, def_id, &poly_sig, deferred)
    })?;

    dbg::check_fn_span!(genv.tcx(), def_id).in_scope(|| Ok(()))
}

fn call_error<'a>(genv: GlobalEnv<'a, '_>, span: Span, dst_span: Option<ESpan>) -> Diag<'a> {
    genv.sess()
        .dcx()
        .create_err(errors::RefineError::call(span, dst_span))
}

fn ret_error<'a>(genv: GlobalEnv<'a, '_>, span: Span, dst_span: Option<ESpan>) -> Diag<'a> {
    genv.sess()
        .dcx()
        .create_err(errors::RefineError::ret(span, dst_span))
}

fn report_errors(
    genv: GlobalEnv,
    local_id: LocalDefId,
    errors: Vec<FixpointCheckError<Tag>>,
) -> Result<(), ErrorGuaranteed> {
    report_errors_with_fixes(genv, local_id, errors, None, &mut FxHashSet::default())
}

fn report_errors_with_fixes(
    genv: GlobalEnv,
    local_id: LocalDefId,
    errors: Vec<FixpointCheckError<Tag>>,
    final_fixes: Option<&UnordMap<rty::WKVid, rty::Binder<rty::Expr>>>,
    emitted_fixes: &mut FxHashSet<DefId>,
) -> Result<(), ErrorGuaranteed> {
    let log_path = if config::dump_constraint() {
        let path = dbg::item_dump_path(genv.tcx(), local_id.to_def_id(), "smt2");
        if path.exists() { Some(path) } else { None }
    } else {
        None
    };
    let mut solutions_by_tag: FxHashMap<Tag, (TagIdx, PossibleSolutions)> = FxHashMap::default();
    for error in errors {
        if let Some((_, val)) = solutions_by_tag.get_mut(&error.tag) {
            val.extend(error.possible_solutions);
        } else {
            solutions_by_tag.insert(error.tag, (error.tag_idx, error.possible_solutions));
        }
    }
    let combined_fn_fix_solutions =
        config::fix_suggestions().then(|| combine_fix_solutions_by_fn(&solutions_by_tag));
    let rerun_note = rerun_hint_note(genv, local_id);
    let mut e = None;
    for (tag, (tag_idx, possible_solutions)) in solutions_by_tag {
        let span = tag.src_span;
        let mut err_diag = match tag.reason {
            ConstrReason::Call
            | ConstrReason::Subtype(SubtypeReason::Input)
            | ConstrReason::Subtype(SubtypeReason::Requires)
            | ConstrReason::Predicate => call_error(genv, span, tag.dst_span),
            ConstrReason::Assign => genv.sess().dcx().create_err(errors::AssignError { span }),
            ConstrReason::Ret
            | ConstrReason::Subtype(SubtypeReason::Output)
            | ConstrReason::Subtype(SubtypeReason::Ensures) => ret_error(genv, span, tag.dst_span),
            ConstrReason::Div => genv.sess().dcx().create_err(errors::DivError { span }),
            ConstrReason::Rem => genv.sess().dcx().create_err(errors::RemError { span }),
            ConstrReason::Goto(_) => genv.sess().dcx().create_err(errors::GotoError { span }),
            ConstrReason::Assert(msg) => {
                genv.sess()
                    .dcx()
                    .create_err(errors::AssertError { span, msg })
            }
            ConstrReason::Fold | ConstrReason::FoldLocal => {
                genv.sess()
                    .dcx()
                    .create_err(errors::FoldError::new(span, tag.dst_span))
            }
            ConstrReason::Overflow => genv.sess().dcx().create_err(errors::OverflowError { span }),
            ConstrReason::Underflow => {
                genv.sess()
                    .dcx()
                    .create_err(errors::UnderflowError { span })
            }
            ConstrReason::Other => genv.sess().dcx().create_err(errors::UnknownError { span }),
            ConstrReason::NoPanic(callee, reason) => {
                genv.sess().dcx().create_err(errors::PanicError {
                    span,
                    callee: genv.tcx().def_path_debug_str(callee),
                    reason: format!("{:?}", reason),
                })
            }
        };
        if let Some(final_fixes) = final_fixes {
            let parent_fn = local_id.to_def_id();
            if !final_fixes.is_empty() && emitted_fixes.insert(parent_fn) {
                add_fn_fix_diagnostic(genv, &mut err_diag, parent_fn, final_fixes);
            }
        } else if let Some(combined_fn_fix_solutions) = &combined_fn_fix_solutions {
            for wkvid in possible_solutions.keys() {
                let parent_fn = wkvid.parent_fn;
                if let Some(wkvar_instantiations) = combined_fn_fix_solutions.get(&parent_fn)
                    && emitted_fixes.insert(parent_fn)
                {
                    add_fn_fix_diagnostic(genv, &mut err_diag, parent_fn, wkvar_instantiations);
                }
            }
        } else {
            let wkvar_solutions = possible_solutions.iter().flat_map(|(wkvid, solutions)| {
                solutions.iter().map(move |solution| (wkvid, solution))
            });
            for (wkvid, solution) in wkvar_solutions {
                let wkvar_instantiations =
                    std::iter::once((wkvid.clone(), solution.clone())).collect::<UnordMap<_, _>>();
                add_fn_fix_diagnostic(genv, &mut err_diag, wkvid.parent_fn, &wkvar_instantiations);
            }
        }
        if let Some(note) = &rerun_note {
            err_diag.note(note.clone());
        }
        if let Some(path) = &log_path {
            err_diag.arg("path", path.display().to_string());
            err_diag.arg("tag", tag_idx.to_string());
            err_diag.note(msg!("log file saved to {$path} (tag: {$tag})"));
        }
        e = Some(err_diag.emit_err());
    }

    if let Some(e) = e { Err(e) } else { Ok(()) }
}

fn combine_fix_solutions_by_fn(
    solutions_by_tag: &FxHashMap<Tag, (TagIdx, PossibleSolutions)>,
) -> FxHashMap<DefId, UnordMap<rty::WKVid, rty::Binder<rty::Expr>>> {
    let mut combined = FxHashMap::default();
    // Cargo fix applies span replacements, so inferred refinements for a function must be
    // conjoined into one replacement rather than emitted as overlapping suggestions.
    for (_, possible_solutions) in solutions_by_tag.values() {
        for (wkvid, solutions) in possible_solutions {
            if solutions.is_empty() {
                continue;
            }
            combined
                .entry(wkvid.parent_fn)
                .or_insert_with(UnordMap::default)
                .entry(wkvid.clone())
                .and_modify(|solution: &mut rty::Binder<rty::Expr>| {
                    *solution =
                        conjoin_solutions([solution.clone()].into_iter().chain(solutions.clone()));
                })
                .or_insert_with(|| conjoin_solutions(solutions.clone()));
        }
    }
    combined
}

fn conjoin_solutions(
    solutions: impl IntoIterator<Item = rty::Binder<rty::Expr>>,
) -> rty::Binder<rty::Expr> {
    let mut solutions = solutions.into_iter();
    let first = solutions.next().unwrap();
    let expr = rty::Expr::and_from_iter(
        std::iter::once(first.skip_binder_ref().clone())
            .chain(solutions.map(|solution| solution.skip_binder())),
    );
    rty::Binder::bind_with_vars(expr, first.vars().clone())
}

fn report_expected_neg(genv: GlobalEnv, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
    Err(genv.sess().emit_err(errors::ExpectedNeg {
        span: genv.tcx().def_span(def_id),
        def_descr: genv.tcx().def_descr(def_id.to_def_id()),
    }))
}

fn add_fn_fix_diagnostic<'a>(
    genv: GlobalEnv<'a, '_>,
    diag: &mut Diag<'a>,
    parent_fn: DefId,
    wkvar_instantiations: &UnordMap<rty::WKVid, rty::Binder<rty::Expr>>,
) {
    let (span, replacement, message) = fn_fix_suggestion(genv, parent_fn, wkvar_instantiations);
    diag.span_suggestion(span, message, replacement, Applicability::MachineApplicable);
}

fn fn_fix_suggestion(
    genv: GlobalEnv,
    parent_fn: DefId,
    wkvar_instantiations: &UnordMap<rty::WKVid, rty::Binder<rty::Expr>>,
) -> (Span, String, &'static str) {
    let wkvar_instantiations = wkvar_instantiations
        .items()
        .map(|(wkvid, solution)| {
            (wkvid.clone(), solution.map_ref(|e| e.simplify(&Default::default()).prettify()))
        })
        .collect();
    let fn_sig = genv.fn_sig(parent_fn).unwrap();
    let mut wkvar_subst = WKVarSubst::new(wkvar_instantiations, false);
    let solved_fn_sig = EarlyBinder(fn_sig.skip_binder_ref().fold_with(&mut wkvar_subst));
    let fixed_fn_sig_snippet = format!(
        "{:?}",
        pretty::with_cx!(&pretty::PrettyCx::default(genv).hide_regions(true), &solved_fn_sig)
    );
    let fn_first_line = fn_first_line(genv, parent_fn);
    let fn_first_line_snippet = genv
        .tcx()
        .sess
        .source_map()
        .span_to_snippet(fn_first_line)
        .unwrap_or_else(|_| panic!("No snippet for span {:?}", fn_first_line));
    let prefix_spaces = &fn_first_line_snippet[..fn_first_line_snippet
        .find(|c: char| !c.is_whitespace())
        .unwrap_or(fn_first_line_snippet.len())];

    // The stored span covers only the signature inside the attribute.
    if let Some(old_spec_span) = genv.spec_attr_span(parent_fn) {
        (old_spec_span, fixed_fn_sig_snippet, "try replacing the refinement")
    } else {
        (
            fn_first_line,
            format!(
                "{}#[flux_rs::sig({})]\n{}",
                prefix_spaces, fixed_fn_sig_snippet, fn_first_line_snippet
            ),
            "try adding the refinement",
        )
    }
}

pub(crate) fn report_standalone_fn_fix(
    genv: GlobalEnv,
    parent_fn: DefId,
    fixes: &UnordMap<rty::WKVid, rty::Binder<rty::Expr>>,
) {
    let (span, replacement, message) = fn_fix_suggestion(genv, parent_fn, fixes);
    let mut diag = genv
        .sess()
        .dcx()
        .struct_span_warn(span, "Flux inferred a refinement for this function");
    diag.span_suggestion(span, message, replacement, Applicability::MachineApplicable);
    diag.emit();
}

fn fn_first_line<'a>(genv: GlobalEnv<'a, '_>, def_id: DefId) -> Span {
    let span = genv.tcx().def_span(def_id);
    let first_line = genv
        .tcx()
        .sess
        .source_map()
        .lookup_line(span.lo())
        .unwrap_or_else(|_| panic!("span for {:?} doesn't have a first line", def_id));
    let first_line_range = first_line.sf.line_bounds(first_line.line);
    Span::new(first_line_range.start, first_line_range.end, span.ctxt(), None)
}

fn rerun_hint_note(genv: GlobalEnv, def_id: LocalDefId) -> Option<String> {
    if !config::rerun_hint() || !config::inside_cargo() {
        return None;
    }
    let pattern = format!("def:{}", genv.tcx().def_path_str(def_id));
    let pkg = std::env::var("CARGO_PKG_NAME")
        .map(|p| format!(" -p {p}"))
        .unwrap_or_default();
    Some(format!("to rerun: `cargo flux check{pkg} --only-check={}`", shell_quote_arg(&pattern)))
}

fn shell_quote_arg(arg: &str) -> String {
    format!("'{}'", arg.replace('\'', "'\\''"))
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::{Diagnostic, Subdiagnostic};
    use flux_middle::rty::ESpan;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag("error jumping to join point", code = E0999)]
    pub struct GotoError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("assignment might be unsafe", code = E0999)]
    pub struct AssignError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Subdiagnostic)]
    #[note("this is the condition that cannot be proved")]
    pub(crate) struct ConditionSpanNote {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Subdiagnostic)]
    #[note("inside this call")]
    pub(crate) struct CallSpanNote {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("refinement type error", code = E0999)]
    pub struct RefineError {
        #[primary_span]
        #[label("a {$cond} cannot be proved")]
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
    #[diag("possible division by zero", code = E0999)]
    pub struct DivError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("possible remainder with a divisor of zero", code = E0999)]
    pub struct RemError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("assertion might fail: {$msg}", code = E0999)]
    pub struct AssertError {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag("type invariant may not hold (when place is folded)", code = E0999)]
    pub struct FoldError {
        #[primary_span]
        pub span: Span,
        #[subdiagnostic]
        span_note: Option<ConditionSpanNote>,
    }

    impl FoldError {
        pub fn new(span: Span, espan: Option<ESpan>) -> Self {
            let span_note = espan.map(|espan| ConditionSpanNote { span: espan.span });
            FoldError { span, span_note }
        }
    }

    #[derive(Diagnostic)]
    #[diag("arithmetic operation may overflow", code = E0999)]
    pub struct OverflowError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("arithmetic operation may underflow", code = E0999)]
    pub struct UnderflowError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("cannot prove this code safe", code = E0999)]
    pub struct UnknownError {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag("{$def_descr} marked with `#[should_fail]` didn't produce a refinement type error", code = E0999)]
    pub struct ExpectedNeg {
        #[primary_span]
        pub span: Span,
        pub def_descr: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag("call to {$callee} may panic: {$reason}", code = E0999)]
    pub(super) struct PanicError {
        #[primary_span]
        pub(super) span: Span,
        pub(super) callee: String,
        pub(super) reason: String,
    }
}
