use flux_common::{iter::IterExt, result::ResultExt};
use flux_errors::ErrorGuaranteed;
use flux_infer::{
    fixpoint_encoding::{FixQueryCache, KVarGen},
    infer::{ConstrReason, InferCtxtRoot, Tag},
};
use flux_middle::{fhir, global_env::GlobalEnv, rty, MaybeExternId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::TypingMode;
use rustc_span::{Span, DUMMY_SP};

use crate::{invoke_fixpoint, CheckerConfig};

pub fn check_invariants(
    genv: GlobalEnv,
    cache: &mut FixQueryCache,
    def_id: MaybeExternId,
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
    cache: &mut FixQueryCache,
    def_id: MaybeExternId,
    adt_def: &rty::AdtDef,
    span: Span,
    invariant: &rty::Invariant,
    checker_config: CheckerConfig,
) -> Result<(), ErrorGuaranteed> {
    let resolved_id = def_id.resolved_id();
    let mut infcx_root =
        InferCtxtRoot::new(genv, resolved_id, KVarGen::dummy(), None).emit(&genv)?;

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
            rcx.assume_invariants(&ty, checker_config.check_overflow);
        }
        let pred = invariant.apply(&variant.idx);
        rcx.check_pred(&pred, Tag::new(ConstrReason::Other, DUMMY_SP));
    }
    let errors =
        invoke_fixpoint(genv, cache, def_id, infcx_root, checker_config, "fluxc").emit(&genv)?;

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
