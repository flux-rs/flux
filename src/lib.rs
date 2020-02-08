#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

#[macro_use]
extern crate rustc;
#[macro_use]
extern crate if_chain;
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

use context::{ErrorReported, LiquidRustCtxt};
use rustc_lint::LateContext;

pub fn run<'a, 'tcx>(
    late_cx: &LateContext<'a, 'tcx>,
    krate: &'tcx rustc_hir::Crate<'tcx>,
) -> Result<(), ErrorReported> {
    let cx = &LiquidRustCtxt::new(late_cx);
    let mut annots = annots::collect(cx, krate)?;

    names::resolve_hir_bindings(cx, &mut annots)?;

    let typeck_table = wf::check_wf(cx, &annots)?;

    let a = ast_lowering::build_fn_refines(cx, &annots[0], &typeck_table);

    typeck::checks(cx, &a, cx.optimized_mir(a.body_id));

    Ok(())
}
