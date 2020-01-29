mod annots;
mod names;
mod syntax;
mod wf;

use crate::context::{ErrorReported, LiquidRustContext};
use rustc_hir::Crate;

pub fn collect_type_annots<'a, 'tcx>(
    cx: &'a LiquidRustContext<'a, 'tcx>,
    krate: &'tcx Crate<'tcx>,
) -> Result<(), ErrorReported> {
    let mut annots = annots::collect(cx, krate)?;

    let mut res = Ok(());
    for fn_annots in &mut annots {
        res = res.and(names::resolve_hir_bindings(cx, fn_annots));
    }
    res?;

    for fn_annots in &mut annots {
        names::resolve_mir_locals(cx, fn_annots);
    }

    res = Ok(());
    for fn_annots in &annots {
        let local_decls = &cx.optimized_mir(fn_annots.body_id).local_decls;
        if let Some(fn_typ) = &fn_annots.fn_ty {
            res = res.and(wf::check_fn_ty(cx, fn_typ, local_decls));
        }
        for refine in fn_annots.locals.values() {
            res = res.and(wf::check_refine(cx, refine, local_decls));
        }
    }
    res?;

    Ok(())
}
