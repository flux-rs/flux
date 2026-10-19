use flux_common::{dbg, dbg::SpanTrace, result::ResultExt as _};
use flux_config as config;
use flux_infer::{
    fixpoint_encoding::{FixQueryCache, FixpointCheckError, PossibleSolutions, SolutionTrace},
    infer::{SavedFixpointQuery, Tag},
};
use flux_middle::{
    FixpointQueryKind,
    global_env::GlobalEnv,
    rty::{self},
};
use rustc_data_structures::{fx::FxHashMap, unord::UnordMap};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::LocalDefId;
use rustc_span::Span;

use crate::{FunctionFixes, report_fixpoint_queries};

pub enum DeferredReport {
    Function(LocalDefId),
    Invariant(Span),
}

pub struct DeferredQuery<'genv, 'tcx> {
    query: SavedFixpointQuery<'genv, 'tcx>,
    report: DeferredReport,
}

impl<'genv, 'tcx> DeferredQuery<'genv, 'tcx> {
    pub fn body(query: SavedFixpointQuery<'genv, 'tcx>, def_id: LocalDefId) -> Self {
        Self { query, report: DeferredReport::Function(def_id) }
    }

    pub fn invariant(query: SavedFixpointQuery<'genv, 'tcx>, span: Span) -> Self {
        Self { query, report: DeferredReport::Invariant(span) }
    }
}

pub fn run(
    genv: GlobalEnv,
    cache: &mut FixQueryCache,
    queries: Vec<DeferredQuery<'_, '_>>,
    fixes: &mut FunctionFixes,
) -> Result<(), ErrorGuaranteed> {
    let mut solutions: FxHashMap<rty::WKVid, rty::Binder<rty::Expr>> = FxHashMap::default();
    let mut final_answers = Vec::new();

    let max_iterations = config::suggestion_max_iterations();
    for iteration in 0..max_iterations {
        let snapshot: UnordMap<_, _> = solutions
            .iter()
            .map(|(wkvid, solution)| (wkvid.clone(), solution.clone()))
            .collect();
        let mut candidates = Vec::new();
        let answers: Vec<_> = queries
            .iter()
            .map(|query| query.query.run(cache, &snapshot))
            .collect();

        for answer in answers.iter().filter_map(|answer| answer.as_ref().ok()) {
            for error in &answer.errors {
                candidates.push(error.possible_solutions.clone());
            }
        }

        let changed = merge_solutions(&mut solutions, candidates);
        final_answers = answers;
        if !changed {
            break;
        }
        if iteration + 1 == max_iterations {
            // The retained diagnostics must correspond to the exact fixes we emit.
            let snapshot: UnordMap<_, _> = solutions
                .iter()
                .map(|(wkvid, solution)| (wkvid.clone(), solution.clone()))
                .collect();
            final_answers = queries
                .iter()
                .map(|query| query.query.run(cache, &snapshot))
                .collect();
        }
    }

    // These are assumptions used by the final check, not its remaining suggestions.
    fixes.extend(solutions.into_iter().filter(|(wkvid, _)| {
        wkvid.parent_fn.is_local()
            && matches!(
                genv.tcx().def_kind(wkvid.parent_fn),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            )
    }));
    let mut errors = None;
    let mut function_errors: FxHashMap<LocalDefId, (Vec<Vec<FixpointCheckError<Tag>>>, bool)> =
        FxHashMap::default();
    let mut invariants = Vec::new();

    for (query, answer) in queries.into_iter().zip(final_answers) {
        let answer = answer.emit(&genv);
        let query_kind = query.query.kind;
        match query.report {
            DeferredReport::Function(def_id) => {
                let (query_errors, query_failed) = function_errors.entry(def_id).or_default();
                match answer {
                    Ok(answer) => {
                        if matches!(query_kind, FixpointQueryKind::Body) {
                            let tcx = genv.tcx();
                            let hir_id = tcx.local_def_id_to_hir_id(def_id);
                            let body_span = tcx.hir_span_with_body(hir_id);
                            dbg::solution!(genv, &answer, body_span);
                        }
                        *query_failed |= !answer.errors.is_empty();
                        query_errors.push(answer.errors);
                    }
                    Err(err) => {
                        *query_failed = true;
                        errors = Some(err).or(errors);
                    }
                }
            }
            DeferredReport::Invariant(span) => {
                match answer {
                    Ok(answer) => invariants.push((span, !answer.errors.is_empty())),
                    Err(err) => errors = Some(err).or(errors),
                }
            }
        }
    }

    for (def_id, (final_errors, query_failed)) in function_errors {
        if let Err(err) = report_fixpoint_queries(genv, def_id, final_errors, query_failed, fixes) {
            errors = Some(err);
        }
    }
    for (span, failed) in invariants {
        if failed {
            errors = Some(crate::invariants::emit_invalid(genv, span));
        }
    }

    errors.map_or(Ok(()), Err)
}

fn merge_solutions(
    solutions: &mut FxHashMap<rty::WKVid, rty::Binder<rty::Expr>>,
    candidates: impl IntoIterator<Item = PossibleSolutions>,
) -> bool {
    let mut changed = false;
    for possible_solutions in candidates {
        for (wkvid, suggestions) in possible_solutions {
            for suggestion in suggestions {
                let suggestion =
                    suggestion.map(|expr| expr.simplify(&Default::default()).erase_metadata());
                for conjunct in suggestion.skip_binder_ref().flatten_conjs() {
                    if conjunct.is_trivially_true() {
                        continue;
                    }
                    let candidate = rty::Binder::bind_with_vars(
                        conjunct.erase_metadata(),
                        suggestion.vars().clone(),
                    );
                    match solutions.get_mut(&wkvid) {
                        Some(existing) => {
                            assert_eq!(
                                existing.vars(),
                                candidate.vars(),
                                "inconsistent WKVar binder shape"
                            );
                            let candidate_expr = candidate.skip_binder_ref();
                            if !existing
                                .skip_binder_ref()
                                .flatten_conjs()
                                .iter()
                                .any(|expr| {
                                    expr.erase_metadata() == candidate_expr.erase_metadata()
                                })
                            {
                                *existing = existing
                                    .clone()
                                    .map(|expr| rty::Expr::and(expr, candidate_expr.clone()));
                                changed = true;
                            }
                        }
                        None => {
                            solutions.insert(wkvid.clone(), candidate);
                            changed = true;
                        }
                    }
                }
            }
        }
    }
    changed
}
