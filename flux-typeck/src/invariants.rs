use flux_common::iter::IterExt;
use flux_errors::ErrorGuaranteed;
use flux_middle::{
    global_env::GlobalEnv,
    rty::{AdtDef, Invariant},
};
use rustc_span::Span;

use crate::{
    constraint_gen::Tag,
    fixpoint::FixpointCtxt,
    refine_tree::{RefineTree, UnpackFlags},
};

pub fn check_invariants(genv: &GlobalEnv, adt_def: &AdtDef) -> Result<(), ErrorGuaranteed> {
    adt_def
        .invariants()
        .iter()
        .enumerate()
        .try_for_each_exhaust(|(idx, invariant)| {
            let span = genv.map().adt(adt_def.def_id().expect_local()).invariants[idx].span;
            check_invariant(genv, adt_def, span, invariant)
        })
}

fn check_invariant(
    genv: &GlobalEnv,
    adt_def: &AdtDef,
    span: Span,
    invariant: &Invariant,
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

        for field in variant.fields() {
            rcx.unpack_with(field, UnpackFlags::INVARIANTS);
        }

        rcx.check_pred(invariant.pred.replace_bound_vars(&variant.ret.indices), Tag::Other);
    }
    let mut fcx = FixpointCtxt::new(genv, Default::default());
    let constraint = refine_tree.into_fixpoint(&mut fcx);
    fcx.check(adt_def.def_id(), constraint)
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
