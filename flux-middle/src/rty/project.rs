use rustc_infer::traits::Obligation;
use rustc_middle::{traits::SelectionError, ty};
use rustc_trait_selection::traits::SelectionContext;

use super::fold::TypeFolder;
use crate::{global_env::GlobalEnv, rty, rty::fold::TypeSuperFoldable};

pub(super) struct Normalizer<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
}

impl<'a, 'tcx> Normalizer<'a, 'tcx> {
    pub(super) fn new(genv: &'a GlobalEnv<'a, 'tcx>) -> Self {
        Self { genv }
    }
}

impl TypeFolder for Normalizer<'_, '_> {
    fn fold_bty(&mut self, bty: &rty::BaseTy) -> rty::BaseTy {
        let rty::BaseTy::Alias(rty::AliasKind::Projection, alias_ty) = bty else {
            return bty.super_fold_with(self);
        };

        normalize_projection_ty(self.genv, alias_ty)
    }
}

fn normalize_projection_ty(genv: &GlobalEnv, alias_ty: &rty::AliasTy) -> rty::BaseTy {
    todo!()
}

fn assemble_candidates_from_param_env<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &rty::AliasTy,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
) {
}

fn assemble_candidates_from_predicates<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &rty::AliasTy,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
    ctor: fn(rty::Binder<rty::ProjectionPredicate>) -> ProjectionCandidate,
    env_predicates: impl Iterator<Item = rty::Clause>,
    potentially_unnormalized_candidates: bool,
) {
    let infcx = selcx.infcx;
    for predicate in env_predicates {
        let bound_predicate = predicate.kind();
        if let rty::ClauseKind::Projection(data) = predicate.kind().skip_binder() {
            let data = bound_predicate.rebind(data);
            if data.projection_def_id() != obligation.def_id {
                continue;
            }

            let is_match = infcx.probe(|_| {
                selcx.match_projection_projections(
                    obligation,
                    data,
                    potentially_unnormalized_candidates,
                )
            });

            match is_match {
                ProjectionMatchesProjection::Yes => {
                    candidate_set.push_candidate(ctor(data));

                    if potentially_unnormalized_candidates
                        && !obligation.predicate.has_non_region_infer()
                    {
                        // HACK: Pick the first trait def candidate for a fully
                        // inferred predicate. This is to allow duplicates that
                        // differ only in normalization.
                        return;
                    }
                }
                ProjectionMatchesProjection::Ambiguous => {
                    candidate_set.mark_ambiguous();
                }
                ProjectionMatchesProjection::No => {}
            }
        }
    }
}

enum ProjectionCandidateSet<'tcx> {
    None,
    Single(ProjectionCandidate),
    Ambiguous,
    Error(SelectionError<'tcx>),
}

enum ProjectionCandidate {
    /// From a where-clause in the env or object type
    ParamEnv(rty::Binder<rty::ProjectionPredicate>),
}
