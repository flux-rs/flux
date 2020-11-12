#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(const_fn)]
#![feature(const_panic)]
#![feature(try_blocks)]

extern crate rustc_arena;
extern crate rustc_mir;
#[macro_use]
extern crate rustc_middle;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_lint;
extern crate rustc_span;
extern crate rustc_target;

pub mod cps_ref;
use rustc_lint::LateContext;

pub fn run<'tcx>(late_cx: &LateContext<'tcx>, krate: &'tcx rustc_hir::Crate<'tcx>) {
    let arena = cps_ref::context::Arena::default();
    let new_cx = cps_ref::context::LiquidRustCtxt::new(&arena);
    for &body_id in &krate.body_ids {
        cps_ref::check_body(&new_cx, late_cx.tcx, body_id)
    }
}
