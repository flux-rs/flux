use flux_common::{iter::IterExt, result::ResultExt};
use flux_config::InferOpts;
use flux_errors::ErrorGuaranteed;
use flux_infer::{
    fixpoint_encoding::FixQueryCache,
    infer::{ConstrReason, GlobalEnvExt, Tag},
};
use flux_middle::{
    FixpointQueryKind, def_id::MaybeExternId, fhir, global_env::GlobalEnv, queries::try_query, rty,
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::TypingMode;
use rustc_span::{DUMMY_SP, Span};

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
    let opts = genv.infer_opts(def_id.local_id());
    adt_def
        .invariants()
        .iter_identity()
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

    let region_infercx = genv
        .tcx()
        .infer_ctxt()
        .with_next_trait_solver(true)
        .build(TypingMode::non_body_analysis());

    let mut infcx_root = try_query(|| {
        genv.infcx_root(&region_infercx, opts)
            .identity_for_item(resolved_id)?
            .build()
    })
    .emit(&genv)?;

    for variant_idx in adt_def.variants().indices() {
        let mut rcx = infcx_root.infcx(resolved_id, &region_infercx);

        let variant_sig = genv
            .variant_sig(adt_def.did(), variant_idx)
            .emit(&genv)?
            .expect("cannot check opaque structs")
            .instantiate_identity()
            .replace_bound_refts_with(|sort, _, _| rty::Expr::fvar(rcx.define_var(sort)));

        for ty in variant_sig.fields() {
            let ty = rcx.unpack(ty);
            rcx.assume_invariants(&ty);
        }
        let pred = invariant.apply(&variant_sig.idx);
        rcx.check_pred(&pred, Tag::new(ConstrReason::Other, DUMMY_SP));
    }
    let answer = infcx_root
        .execute_fixpoint_query(cache, def_id, FixpointQueryKind::Invariant)
        .emit(&genv)?;

    if answer.errors.is_empty() {
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
