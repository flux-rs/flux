use flux_common::{cache::QueryCache, dbg, iter::IterExt, result::ResultExt};
use flux_config as config;
use flux_errors::ErrorGuaranteed;
use flux_middle::{fhir, global_env::GlobalEnv, rty};
use rustc_hir::def_id::LocalDefId;
use rustc_span::{Span, DUMMY_SP};

use crate::{
    constraint_gen::{ConstrReason, Tag},
    fixpoint_encoding::{FixpointCtxt, KVarStore},
    refine_tree::RefineTree,
    CheckerConfig,
};

pub fn check_invariants(
    genv: GlobalEnv,
    cache: &mut QueryCache,
    def_id: LocalDefId,
    invariants: &[fhir::Expr],
    adt_def: &rty::AdtDef,
    checker_config: CheckerConfig,
) -> Result<(), ErrorGuaranteed> {
    adt_def
        .invariants()
        .iter()
        .enumerate()
        .try_for_each_exhaust(|(idx, invariant)| {
            let span = invariants[idx].span;
            check_invariant(genv, cache, def_id, adt_def, span, invariant, checker_config)
        })
}

fn check_invariant(
    genv: GlobalEnv,
    cache: &mut QueryCache,
    def_id: LocalDefId,
    adt_def: &rty::AdtDef,
    span: Span,
    invariant: &rty::Invariant,
    checker_config: CheckerConfig,
) -> Result<(), ErrorGuaranteed> {
    let mut refine_tree = RefineTree::new();

    for variant_idx in adt_def.variants().indices() {
        let mut rcx = refine_tree.refine_ctxt_at_root();

        let variant = genv
            .variant_sig(adt_def.did(), variant_idx)
            .emit(&genv)?
            .expect("cannot check opaque structs")
            .instantiate_identity(&[])
            .replace_bound_refts_with(|sort, _, _| rcx.define_vars(sort));

        for ty in variant.fields() {
            let ty = rcx.unpack(ty);
            rcx.assume_invariants(&ty, checker_config.check_overflow);
        }
        let pred = invariant.apply(&variant.idx);
        rcx.check_pred(&pred, Tag::new(ConstrReason::Other, DUMMY_SP));
    }
    let mut fcx = FixpointCtxt::new(genv, def_id, KVarStore::default()).emit(&genv)?;
    if config::dump_constraint() {
        dbg::dump_item_info(genv.tcx(), def_id, "fluxc", &refine_tree).unwrap();
    }

    let cstr = refine_tree.into_fixpoint(&mut fcx).emit(&genv)?;
    let errors = fcx.check(cache, cstr, &checker_config).emit(&genv)?;
    if errors.is_empty() {
        Ok(())
    } else {
        Err(genv.sess().emit_err(errors::Invalid { span }))
    }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(refineck_invalid_invariant, code = E0999)]
    pub struct Invalid {
        #[primary_span]
        pub span: Span,
    }
}
