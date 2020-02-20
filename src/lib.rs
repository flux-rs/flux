#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate arena;
#[macro_use]
extern crate rustc;
#[macro_use]
extern crate if_chain;
extern crate rustc_apfloat;
extern crate rustc_data_structures;
extern crate rustc_hir;
#[macro_use]
extern crate rustc_index;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_span;
extern crate serialize as rustc_serialize;

pub mod annots;
pub mod context;
pub mod names;
pub mod refinements;
pub mod reft_lowering;
pub mod smtlib2;
pub mod syntax;
pub mod wf;

use context::{ArenaInterner, ErrorReported, LiquidRustCtxt};
use refinements::typeck;
use rustc_lint::LateContext;

pub fn run<'a, 'tcx>(
    late_cx: &LateContext<'a, 'tcx>,
    krate: &'tcx rustc_hir::Crate<'tcx>,
) -> Result<(), ErrorReported> {
    let preds = ArenaInterner::new(arena::TypedArena::default());
    let refts = ArenaInterner::new(arena::TypedArena::default());
    let mut cx = LiquidRustCtxt::new(late_cx, &preds, &refts);
    let mut annots = annots::collect(&cx, krate)?;

    names::resolve_hir_bindings(&cx, &mut annots)?;

    let typeck_table = wf::check_wf(&cx, &annots)?;

    let refts = reft_lowering::build_refts(&cx, &annots, &typeck_table)?;

    for body_refts in refts {
        cx.add_body_refts(body_refts)
    }

    for body_annots in annots {
        typeck::check_body(&cx, body_annots.body_id)
    }

    Ok(())
}
