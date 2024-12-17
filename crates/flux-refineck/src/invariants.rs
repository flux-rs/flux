use flux_common::{iter::IterExt, result::ResultExt};
use flux_errors::ErrorGuaranteed;
use flux_infer::{
    fixpoint_encoding::FixQueryCache,
    infer::{ConstrReason, GlobalEnvExt, InferOpts, Tag},
};
use flux_middle::{fhir, global_env::GlobalEnv, rty, MaybeExternId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::TypingMode;
use rustc_span::{Span, DUMMY_SP};

pub fn check_invariants(
    genv: GlobalEnv,
    cache: &mut FixQueryCache,
    def_id: MaybeExternId,
    invariants: &[fhir::Expr],
    adt_def: &rty::AdtDef,
) -> Result<(), ErrorGuaranteed> {
    // FIXME(nilehmann) maybe we should record whether the invariants were generated with overflow
    // checking enabled and only assume them in code that also overflow checking enabled.
    // Although, enable overflow checking locally is unsound in general.
    //
    // The good way would be to make overflow checking a property of a type that can be turned on
    // and off locally. Then we consider an overflow-checked `T` distinct from a non-checked one and
    // error/warn in case of a mismatch: overflow-checked types can flow to non-checked code but not
    // the other way around.
    let opts =
        InferOpts { check_overflow: genv.check_overflow(def_id.local_id()), scrape_quals: false };
    adt_def
        .invariants()
        .iter()
        .enumerate()
        .try_for_each_exhaust(|(idx, invariant)| {
            let span = invariants[idx].span;
            check_invariant(genv, cache, def_id, adt_def, span, invariant, opts)
        })
}

fn check_invariant(
    genv: GlobalEnv,
    cache: &mut FixQueryCache,
    def_id: MaybeExternId,
    adt_def: &rty::AdtDef,
    span: Span,
    invariant: &rty::Invariant,
    opts: InferOpts,
) -> Result<(), ErrorGuaranteed> {
    let resolved_id = def_id.resolved_id();
    let mut infcx_root = genv.infcx_root(resolved_id, opts).build().emit(&genv)?;

    let region_infercx = genv
        .tcx()
        .infer_ctxt()
        .build(TypingMode::non_body_analysis());
    for variant_idx in adt_def.variants().indices() {
        let mut rcx = infcx_root.infcx(resolved_id, &region_infercx);

        let variant = genv
            .variant_sig(adt_def.did(), variant_idx)
            .emit(&genv)?
            .expect("cannot check opaque structs")
            .instantiate_identity()
            .replace_bound_refts_with(|sort, _, _| rcx.define_vars(sort));

        for ty in variant.fields() {
            let ty = rcx.unpack(ty);
            rcx.assume_invariants(&ty);
        }
        let pred = invariant.apply(&variant.idx);
        rcx.check_pred(&pred, Tag::new(ConstrReason::Other, DUMMY_SP));
    }
    let errors = infcx_root
        .execute_fixpoint_query(cache, def_id, "fluxc")
        .emit(&genv)?;

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
