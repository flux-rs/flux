#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate arena;
extern crate rustc;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_lint;
extern crate rustc_span;

pub mod annots;
pub mod ast_lowering;
pub mod context;
pub mod names;
pub mod refinements;
pub mod smtlib2;
pub mod syntax;
pub mod typeck;
pub mod wf;

use arena::TypedArena;
use context::{ErrorReported, LiquidRustCtxt};
use refinements::RefineCtxt;
use rustc_lint::LateContext;

pub fn run<'a, 'tcx>(
    late_cx: &LateContext<'a, 'tcx>,
    krate: &'tcx rustc_hir::Crate<'tcx>,
) -> Result<(), ErrorReported> {
    let cx = &LiquidRustCtxt::new(late_cx);
    let arena = TypedArena::default();
    let rcx = RefineCtxt::new(late_cx.tcx, &arena);
    let mut annots = annots::collect(cx, krate)?;

    names::resolve_hir_bindings(cx, &mut annots)?;

    let typeck_table = wf::check_wf(cx, &annots)?;

    // let a = ast_lowering::build_refines(cx, &rcx, &annots, &typeck_table)?;
    let (a, mut var_subst) = ast_lowering::build_fn_refines(cx, &rcx, &annots[0], &typeck_table);

    typeck::checks(cx, &rcx, &a, cx.optimized_mir(a.body_id), &mut var_subst);

    Ok(())
}
