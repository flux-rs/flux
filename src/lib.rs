#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(const_fn)]
#![feature(const_panic)]
#![feature(try_blocks)]

extern crate rustc_arena;
extern crate rustc_ast;
#[macro_use]
extern crate rustc_middle;
#[macro_use]
extern crate if_chain;
extern crate rustc_apfloat;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_span;
extern crate rustc_target;

pub mod annots;
pub mod context;
pub mod cps;
pub mod names;
pub mod refinements;
pub mod reft_lowering;
pub mod smtlib2;
pub mod syntax;
pub mod wf;

use context::{ArenaInterner, ErrorReported, LiquidRustCtxt};
use refinements::typeck;
use rustc_lint::LateContext;

pub fn run<'tcx>(
    late_cx: &LateContext<'tcx>,
    krate: &'tcx rustc_hir::Crate<'tcx>,
) -> Result<(), ErrorReported> {
    try {
        let preds = ArenaInterner::new(rustc_arena::TypedArena::default());
        let refts = ArenaInterner::new(rustc_arena::TypedArena::default());
        let mut cx = LiquidRustCtxt::new(late_cx, &preds, &refts);
        let mut annots = annots::collect(&cx, krate)?;

        names::resolve_hir_bindings(&cx, &mut annots)?;

        let reft_table = wf::check_wf(&cx, &annots)?;

        let refts = reft_lowering::build_refts(&cx, &annots, &reft_table)?;

        for body_refts in refts {
            cx.add_body_refts(body_refts)
        }

        for body_annots in annots {
            typeck::check_body(&cx, body_annots.body_id)
        }
    }
}
