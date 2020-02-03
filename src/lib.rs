#![feature(rustc_private)]
#![feature(box_syntax)]

extern crate rustc;
extern crate rustc_hir;
extern crate rustc_lint;
extern crate rustc_span;

pub mod annots;
pub mod context;
pub mod names;
pub mod syntax;
pub mod ty;
pub mod wf;

use context::{ErrorReported, LiquidRustContext};
use rustc_lint::LateContext;

pub fn run<'a, 'tcx>(
    late_cx: &LateContext<'a, 'tcx>,
    krate: &'tcx rustc_hir::Crate<'tcx>,
) -> Result<(), ErrorReported> {
    let cx = &LiquidRustContext::new(late_cx);

    let mut annots = annots::collect(cx, krate)?;

    names::resolve_hir_bindings(cx, &mut annots)?;

    // names::resolve_mir_locals(cx, &mut annots);

    wf::check_wf(cx, &annots)?;

    Ok(())
}
