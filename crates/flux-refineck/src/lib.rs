//! Refinement type checking

#![feature(
    associated_type_defaults,
    box_patterns,
    if_let_guard,
    min_specialization,
    never_type,
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
mod ghost_statements;
pub mod invariants;
mod primops;
mod queue;
mod type_env;

use std::collections::HashMap;

use checker::{Checker, trait_impl_subtyping};
use flux_common::{dbg, dbg::SpanTrace, result::ResultExt as _};
use flux_config as config;
use flux_infer::{
    fixpoint_encoding::{FixQueryCache, FixpointCheckError, SolutionTrace},
    infer::{ConstrReason, SubtypeReason, Tag},
    refine_tree::{BinderDeps, BinderOriginator, BinderProvenance, CallReturn},
    wkvars::{Constraints, WKVarSubst},
};
use flux_macros::fluent_messages;
use flux_middle::{
    FixpointQueryKind,
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    metrics::{self, Metric, TimingKind},
    pretty,
    rty::{
        self, ESpan, EarlyBinder, Name,
        fold::{TypeFoldable, TypeVisitable},
    },
};
use rustc_data_structures::{fx::FxHashSet, unord::UnordMap};
use rustc_errors::{Applicability, Diag, ErrorGuaranteed};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_span::{FileNameDisplayPreference, Span, source_map::SourceMap};
use serde::{Serialize, Serializer, ser::SerializeSeq};

use crate::{checker::errors::ResultExt as _, ghost_statements::compute_ghost_statements};

fluent_messages! { "../locales/en-US.ftl" }

pub fn report_fixpoint_errors(
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

/// Report inferred annotations as suggestions (for non-interactive Wick mode)
pub fn report_inferred_annotations(
    genv: GlobalEnv,
    solutions: &flux_infer::wkvars::WKVarSolutions,
) {
    use rustc_data_structures::fx::FxIndexMap;
    
    // Group solutions by function
    let mut solutions_by_fn: FxIndexMap<DefId, Vec<(rty::WKVid, rty::Binder<rty::Expr>)>> = FxIndexMap::default();
    
    for (wkvid, solution) in &solutions.solutions {
        if let Some(subst) = solution.into_wkvar_subst() {
            solutions_by_fn
                .entry(wkvid.parent_fn)
                .or_default()
                .push((wkvid.clone(), subst));
        }
    }
    
    // Create one diagnostic per function with all solutions combined
    for (def_id, wkvar_solutions) in solutions_by_fn {
        if wkvar_solutions.is_empty() {
            continue;
        }
        
        let fn_span = genv.tcx().def_span(def_id);
        let fn_name = genv.tcx().def_path_str(def_id);
        
        // Create a help diagnostic with suggestion
        let mut diag = genv.sess().dcx().handle().struct_help(
            format!("Inferred annotation for `{}`", fn_name)
        );
        diag.span(fn_span);
        
        // Combine all wkvar solutions into a single substitution
        let fn_sig = genv.fn_sig(def_id).unwrap();
        let mut combined_subst_map = FxIndexMap::default();
        for (wkvid, solution) in wkvar_solutions {
            let pretty_solution = solution.map_ref(|e| e.simplify(&Default::default()).prettify());
            combined_subst_map.insert(wkvid, pretty_solution);
        }
        
        let mut wkvar_subst = WKVarSubst::new(combined_subst_map.into_iter().collect(), false);
        let solved_fn_sig = EarlyBinder(fn_sig.skip_binder_ref().fold_with(&mut wkvar_subst));
        let fixed_fn_sig_snippet = format!(
            "{:?}",
            pretty::with_cx!(&pretty::PrettyCx::default(genv).hide_regions(true), &solved_fn_sig)
        );
        let fn_first_line = fn_first_line(genv, def_id);
        let fn_first_line_snippet = genv
            .tcx()
            .sess
            .source_map()
            .span_to_snippet(fn_first_line)
            .unwrap_or_else(|_| panic!("No snippet for span {:?}", fn_first_line));
        let prefix_spaces = &fn_first_line_snippet[..fn_first_line_snippet
            .find(|c: char| !c.is_whitespace())
            .unwrap_or(fn_first_line_snippet.len())];
        
        diag.span_suggestion(
            fn_first_line,
            "try adding the refinement",
            format!("{}#[sig({})]\n{}", prefix_spaces, fixed_fn_sig_snippet, fn_first_line_snippet),
            Applicability::MachineApplicable,
        );
        
        diag.emit();
    }
}

pub fn check_fn(
    genv: GlobalEnv,
    cache: &mut FixQueryCache,
    constraints: &mut Constraints,
    def_id: LocalDefId,
) -> Result<(), ErrorGuaranteed> {
    let span = genv.tcx().def_span(def_id);

    // HACK(nilehmann) this will ignore any code generated by a macro. This is a temporary
    // workaround to deal with a `#[derive(..)]` that generates code that flux cannot handle.
    // Note that this is required because code generated by a `#[derive(..)]` cannot be
    // manually trusted or ignored.
    if !genv.tcx().def_span(def_id).ctxt().is_root() {
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
        let answer = infcx_root
            .execute_fixpoint_query_collecting_constraints(
                cache,
                constraints,
                MaybeExternId::Local(def_id),
                FixpointQueryKind::Impl,
            )
            .emit(&genv)?;
        tracing::info!("check_fn::fixpoint-subtyping");
        let errors = answer.errors;
        report_fixpoint_errors(genv, def_id, errors)?;
    }

    // Skip trusted functions
    if genv.trusted(def_id) {
        metrics::incr_metric(Metric::FnTrusted, 1);
        return Ok(());
    }

    metrics::incr_metric(Metric::FnChecked, 1);
    metrics::time_it(TimingKind::CheckFn(def_id), || -> Result<(), ErrorGuaranteed> {
        let ghost_stmts = compute_ghost_statements(genv, def_id)
            .with_span(span)
            .map_err(|err| err.emit(genv, def_id))?;
        let mut closures = UnordMap::default();
        // PHASE 1: infer shape of `TypeEnv` at the entry of join points
        let shape_result =
            Checker::run_in_shape_mode(genv, def_id, &ghost_stmts, &mut closures, opts)
                .map_err(|err| err.emit(genv, def_id))?;

        // PHASE 2: generate refinement tree constraint
        let infcx_root = Checker::run_in_refine_mode(
            genv,
            def_id,
            &ghost_stmts,
            &mut closures,
            shape_result,
            opts,
        )
        .map_err(|err| err.emit(genv, def_id))?;

        if genv.proven_externally(def_id) {
            if flux_config::emit_lean_defs() {
                infcx_root
                    .execute_lean_query(MaybeExternId::Local(def_id))
                    .emit(&genv)
            } else {
                panic!("emit_lean_defs should be enabled if there are externally proven items");
            }
        } else {
            // PHASE 3: invoke fixpoint on the constraint
            let answer = infcx_root
                .execute_fixpoint_query_collecting_constraints(
                    cache,
                    constraints,
                    MaybeExternId::Local(def_id),
                    FixpointQueryKind::Body,
                )
                .emit(&genv)?;

            // DUMP SOLUTION
            let tcx = genv.tcx();
            let hir_id = tcx.local_def_id_to_hir_id(def_id);
            let body_span = tcx.hir_span_with_body(hir_id);
            dbg::solution!(genv, &answer.solution, body_span);

            let errors = answer.errors;
            report_fixpoint_errors(genv, def_id, errors)
        }
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
            | ConstrReason::Subtype(SubtypeReason::Requires)
            | ConstrReason::Predicate => call_error(genv, span, err.tag.dst_span),
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
            ConstrReason::Underflow => {
                genv.sess()
                    .dcx()
                    .handle()
                    .create_err(errors::UnderflowError { span })
            }
        };

        let subst = make_binder_subst(genv, &err.blame_ctx.blame_analysis.binder_deps);
        let binders =
            binders_from_expr(&err.blame_ctx.expr, &err.blame_ctx.blame_analysis.binder_deps);
        // Current heuristic:
        //   * We examine each binder from the expression
        //   * Binders are sorted in order of how useful they are (most-to-least)
        //     - Right now this is by how deep they are in the generated flux expression
        //   * We can blame a binder if
        //     - It comes from a function (and has a function we can show a span for)
        //     - It is a function argument
        //   * The rest are related (we reverse the sort to emit them most-to-least useful)
        let (blamed_binders, _related_binders) = split_binders(binders);

        // // Find predicates which imply the failing constraint
        // let solution_candidates = _find_solution_candidates(&err.blame_ctx);

        let wkvar_solutions = err
            .possible_solutions
            .iter()
            .flat_map(|(wkvid, solutions)| solutions.iter().map(move |solution| (wkvid, solution)));

        if config::debug_binder_output() {
            // FIXME: We don't render the wk kvar suggestions in the debug output.
            let binder_debug_infos = collect_binder_debug_info(
                genv,
                &err.blame_ctx.expr,
                &err.blame_ctx.blame_analysis.binder_deps,
                &subst,
            );
            let blame_spans = blamed_binders
                .into_iter()
                .map(|binder_info| {
                    let span = match binder_info.originator {
                        BinderOriginator::CallReturn(CallReturn {
                            def_id: Some(def_id), ..
                        }) => {
                            genv.tcx()
                                .def_ident_span(def_id)
                                .unwrap_or_else(|| genv.tcx().def_span(def_id))
                        }
                        _ => binder_info.span,
                    };
                    BlameSpanDebugInfo {
                        binder_name: binder_info.name,
                        blame_span: SimpleSpan::from_span(span, genv.tcx().sess.source_map()),
                        // We don't emit right now.
                        suggested_refinement: None,
                    }
                })
                .collect();
            // Note that we don't need to bother collecting info on the rest of the related vars because
            // we already got information on them from the binder_deps.
            let constraint_debug_info = ConstraintDebugInfo {
                constraint: err.blame_ctx.expr,
                binders: binder_debug_infos,
                blame_spans,
            };
            let debug_str = format!(
                "constraint_debug_info: {}",
                serde_json::to_string(&constraint_debug_info).unwrap()
            );
            err_diag.note(debug_str);
        } else {
            // let pred_pretty_cx = pretty::PrettyCx::default(genv).with_free_var_substs(subst);
            // err_diag.subdiagnostic(errors::FailingConstraint {
            //     constraint: format!("{:?}", pretty::with_cx!(&pred_pretty_cx, &err.blame_ctx.expr)),
            // });
            for (wkvid, solution) in wkvar_solutions {
                add_fn_fix_diagnostic(genv, &mut err_diag, wkvid.clone(), solution);
            }
            // (previous helpers for blame/related var diagnostics removed; not used)
        }

        e = Some(err_diag.emit());
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
fn binders_from_expr(expr: &rty::Expr, binder_deps: &BinderDeps) -> Vec<BinderInfo> {
    let mut binders: Vec<BinderInfo> = expr
        .fvars()
        .iter()
        .filter_map(|name| {
            // We can only report information for variables which
            // 1. We have information for (this should be all variables...)
            binder_deps
                .get(name)
                .and_then(|(bp_opt, depth, _related_vars)| {
                    // 2. Have a provenance.
                    bp_opt.as_ref().and_then(|bp| {
                        // 3. Have a span
                        bp.span.map(|span| {
                            BinderInfo {
                                name: *name,
                                span,
                                originator: bp.originator.clone(),
                                depth: *depth,
                            }
                        })
                    })
                })
        })
        .collect();
    binders.sort_by_key(|bi| std::cmp::Reverse(bi.depth));
    binders
}

fn make_binder_subst(genv: GlobalEnv, binder_deps: &BinderDeps) -> HashMap<Name, String> {
    let mut subst = HashMap::new();
    binder_deps
        .iter()
        .for_each(|(name, (bp_opt, _depth, _related_vars))| {
            if let Some(bp) = bp_opt.as_ref() {
                add_substitution_for_binder_var(genv, &mut subst, *name, bp);
            }
        });
    subst
}

/// Splits a list of binders into ones which we blame and ones which are just
/// related.
///
/// Right now the heuristic is to blame any binder we _can_, which are:
///   1. Function arguments
///   2. The return values of functions
fn split_binders(binders: Vec<BinderInfo>) -> (Vec<BinderInfo>, Vec<BinderInfo>) {
    let mut blamed_binders = Vec::new();
    let mut related_binders = Vec::new();
    for binder in binders {
        match binder.originator {
            BinderOriginator::FnArg(_) => blamed_binders.push(binder),
            BinderOriginator::CallReturn(CallReturn { def_id: Some(_), .. }) => {
                blamed_binders.push(binder);
            }
            _ => related_binders.push(binder),
        }
    }
    (blamed_binders, related_binders)
}

fn add_fn_fix_diagnostic<'a>(
    genv: GlobalEnv<'a, '_>,
    diag: &mut Diag<'a>,
    wkvid: rty::WKVid,
    solution: &rty::Binder<rty::Expr>,
) {
    let pretty_solution = solution.map_ref(|e| e.simplify(&Default::default()).prettify());
    let fn_sig = genv.fn_sig(wkvid.parent_fn).unwrap();
    let mut wkvar_subst = WKVarSubst::new([(wkvid.clone(), pretty_solution)].into(), false);
    let solved_fn_sig = EarlyBinder(fn_sig.skip_binder_ref().fold_with(&mut wkvar_subst));
    let fixed_fn_sig_snippet = format!(
        "{:?}",
        pretty::with_cx!(&pretty::PrettyCx::default(genv).hide_regions(true), &solved_fn_sig)
    );
    let fn_first_line = fn_first_line(genv, wkvid.parent_fn);
    let fn_first_line_snippet = genv
        .tcx()
        .sess
        .source_map()
        .span_to_snippet(fn_first_line)
        .unwrap_or_else(|_| panic!("No snippet for span {:?}", fn_first_line));
    let prefix_spaces = &fn_first_line_snippet[..fn_first_line_snippet
        .find(|c: char| !c.is_whitespace())
        .unwrap_or(fn_first_line_snippet.len())];
    let subst_solutions = &wkvar_subst.subst_instantiations[&wkvid];
    assert!(subst_solutions.len() == 1);
    diag.span_suggestion(
        fn_first_line,
        "try adding the refinement",
        format!("{}#[sig({})]\n{}", prefix_spaces, fixed_fn_sig_snippet, fn_first_line_snippet),
        Applicability::MaybeIncorrect,
    );
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

// Note: helper diagnostics for blaming variables were removed because they were never used.

#[derive(Debug, Clone)]
struct BinderInfo {
    name: Name,
    span: Span,
    originator: BinderOriginator,
    depth: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct SimpleLoc {
    /// 1-based line number.
    pub line: usize,
    /// 1-based character offset.
    pub char: usize,
    /// The source file name.
    pub file: String,
}

#[derive(Debug, Clone, Serialize)]
/// A simplified version of [`Span`] suitable for debug output.
pub struct SimpleSpan {
    pub start: SimpleLoc,
    pub end: SimpleLoc,
}

impl SimpleSpan {
    fn from_span(span: Span, sm: &SourceMap) -> Option<Self> {
        if span.is_dummy() {
            return None;
        }

        let start_loc_data = sm.lookup_char_pos(span.lo());
        let end_loc_data = sm.lookup_char_pos(span.hi());

        // `loc.col` is 0-based, so add 1 for a 1-based character offset.
        let start = SimpleLoc {
            file: start_loc_data
                .file
                .name
                .display(FileNameDisplayPreference::Local)
                .to_string(),
            line: start_loc_data.line,
            char: start_loc_data.col.0 + 1,
        };

        let end = SimpleLoc {
            file: end_loc_data
                .file
                .name
                .display(FileNameDisplayPreference::Local)
                .to_string(),
            line: end_loc_data.line,
            char: end_loc_data.col.0 + 1,
        };

        Some(SimpleSpan { start, end })
    }
}

#[derive(Debug, Clone, Serialize)]
struct SimpleFnInfo {
    fn_name: String,
    fn_span: Option<SimpleSpan>,
}

#[derive(Debug, Clone, Serialize)]
struct BinderDebugInfo {
    #[serde(serialize_with = "serialize_debug")]
    name: Name,
    pretty_name: Option<String>,
    span: Option<SimpleSpan>,
    #[serde(serialize_with = "serialize_debug")]
    originator: Option<BinderOriginator>,
    depth: usize,
    #[serde(serialize_with = "serialize_set_debug")]
    related_vars: FxHashSet<Name>,
    in_constraint: bool,
    related_function: Option<SimpleFnInfo>,
}

#[derive(Debug, Clone, Serialize)]
struct BlameSpanDebugInfo {
    #[serde(serialize_with = "serialize_debug")]
    binder_name: Name,
    /// The span where the fix goes (this is not always the binder's location)
    blame_span: Option<SimpleSpan>,
    /// What refinement does this need added to it?
    suggested_refinement: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ConstraintDebugInfo {
    #[serde(serialize_with = "serialize_debug")]
    constraint: rty::Expr,
    binders: Vec<BinderDebugInfo>,
    blame_spans: Vec<BlameSpanDebugInfo>,
}

fn serialize_debug<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
where
    T: std::fmt::Debug,
    S: Serializer,
{
    serializer.serialize_str(&format!("{:?}", value))
}

fn serialize_set_debug<T, S>(set: &FxHashSet<T>, serializer: S) -> Result<S::Ok, S::Error>
where
    T: std::fmt::Debug,
    S: Serializer,
{
    let mut seq = serializer.serialize_seq(Some(set.len()))?;

    for name in set {
        let name_debug_str = format!("{:?}", name);

        seq.serialize_element(&name_debug_str)?;
    }

    seq.end()
}

fn collect_binder_debug_info(
    genv: GlobalEnv,
    expr: &rty::Expr,
    binder_deps: &BinderDeps,
    pretty_name_subst: &HashMap<Name, String>,
) -> Vec<BinderDebugInfo> {
    let expr_vars = expr.fvars();
    binder_deps
        .iter()
        .map(|(name, (bp, depth, related_vars))| {
            BinderDebugInfo {
                name: *name,
                pretty_name: pretty_name_subst.get(name).cloned(),
                span: bp.clone().and_then(|bp| {
                    bp.span
                        .and_then(|span| SimpleSpan::from_span(span, genv.tcx().sess.source_map()))
                }),
                originator: bp.clone().map(|bp| bp.originator.clone()),
                depth: *depth,
                related_vars: related_vars.clone(),
                in_constraint: expr_vars.contains(name),
                related_function: bp.clone().and_then(|bp| {
                    match bp.originator {
                        BinderOriginator::CallReturn(CallReturn {
                            def_id: Some(def_id), ..
                        }) => {
                            let fn_name = genv.tcx().def_path_str(def_id);
                            let fn_span = genv
                                .tcx()
                                .def_ident_span(def_id)
                                .unwrap_or_else(|| genv.tcx().def_span(def_id));
                            Some(SimpleFnInfo {
                                fn_name,
                                fn_span: SimpleSpan::from_span(
                                    fn_span,
                                    genv.tcx().sess.source_map(),
                                ),
                            })
                        }
                        _ => None,
                    }
                }),
            }
        })
        .collect()
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
    #[diag(refineck_underflow_error, code = E0999)]
    pub struct UnderflowError {
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

    // Several subdiagnostic helpers and notes were removed because they are
    // never constructed or referenced in the current codepath. Keeping the
    // set of diagnostics minimal avoids dead-code warnings; if these are
    // needed in the future they can be reintroduced with proper usage.

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
