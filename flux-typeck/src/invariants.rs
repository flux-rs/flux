use flux_middle::{
    global_env::GlobalEnv,
    ty::{AdtDef, Binders, Expr, TyKind},
};

use crate::{
    constraint_gen::Tag,
    fixpoint::FixpointCtxt,
    refine_tree::{RefineTree, UnpackFlags},
};

pub fn check_invariants(genv: &GlobalEnv, adt_def: &AdtDef) {
    for invariant in adt_def.invariants() {
        check_invariant(genv, adt_def, invariant);
    }
}

fn check_invariant(genv: &GlobalEnv, adt_def: &AdtDef, invariant: &Binders<Expr>) {
    let mut refine_tree = RefineTree::new();

    for variant_idx in adt_def.variants() {
        let mut rcx = refine_tree.refine_ctxt_at_root();

        let mut names = vec![];
        let variant = genv
            .variant(adt_def.def_id(), variant_idx)
            .replace_bvars_with_fresh_fvars(|sort| {
                let fresh = rcx.define_var(sort);
                names.push(fresh);
                fresh
            });

        for field in variant.fields() {
            rcx.unpack_with(field, UnpackFlags::INVARIANTS);
        }

        if let TyKind::Indexed(_, idxs) = variant.ret.kind() {
            // TODO(nilehmann) maybe parameterize RefineTree by the tag so we can use
            // a different Tag type here
            rcx.check_pred(invariant.replace_bound_vars(&idxs.to_exprs()), Tag::Other);
        } else {
            panic!()
        }
    }
    let mut fcx = FixpointCtxt::new(&genv.consts, Default::default());
    let constraint = refine_tree.into_fixpoint(&mut fcx);
    fcx.check(genv.tcx, adt_def.def_id(), constraint, &[], &genv.uf_sorts)
        .unwrap();
}
