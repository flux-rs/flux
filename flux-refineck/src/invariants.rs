use flux_common::{cache::QueryCache, iter::IterExt};
use flux_errors::ErrorGuaranteed;
use flux_middle::{fhir, global_env::GlobalEnv, rty};
use rustc_span::{Span, DUMMY_SP};

use crate::{
    constraint_gen::{ConstrReason, Tag},
    fixpoint::{FixpointCtxt, KVarStore},
    refine_tree::RefineTree,
};

pub fn check_invariants(
    genv: &GlobalEnv,
    cache: &mut QueryCache,
    invariants: &[fhir::Expr],
    adt_def: &rty::AdtDef,
) -> Result<(), ErrorGuaranteed> {
    adt_def
        .invariants()
        .iter()
        .enumerate()
        .try_for_each_exhaust(|(idx, invariant)| {
            let span = invariants[idx].span;
            check_invariant(genv, cache, adt_def, span, invariant)
        })
}

fn check_invariant(
    genv: &GlobalEnv,
    cache: &mut QueryCache,
    adt_def: &rty::AdtDef,
    span: Span,
    invariant: &rty::Invariant,
) -> Result<(), ErrorGuaranteed> {
    let mut refine_tree = RefineTree::new();

    for variant_idx in adt_def.variants() {
        let mut rcx = refine_tree.refine_ctxt_at_root();

        let mut names = vec![];
        let variant = genv
            .variant(adt_def.def_id(), variant_idx)
            .expect("cannot check opaque structs")
            .replace_bvars_with_fresh_fvars(|sort| {
                let fresh = rcx.define_var(sort);
                names.push(fresh);
                fresh
            });

        for ty in variant.fields() {
            let ty = rcx.unpack(ty);
            rcx.assume_invariants(&ty);
        }
        let (.., idxs) = variant.ret.expect_adt();
        rcx.check_pred(
            invariant.pred.replace_bvars(idxs.args()),
            Tag::new(ConstrReason::Other, DUMMY_SP),
        );
    }
    let mut fcx = FixpointCtxt::new(genv, KVarStore::default());
    let constraint = refine_tree.into_fixpoint(&mut fcx);
    fcx.check(cache, adt_def.def_id(), constraint)
        .map_err(|_| genv.sess.emit_err(errors::Invalid { span }))
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(invariants::invalid, code = "FLUX")]
    pub struct Invalid {
        #[primary_span]
        pub span: Span,
    }
}
