extern crate arena;
extern crate rustc_errors;
extern crate rustc_lint;
extern crate rustc_session;

use super::refinements::{self, BodyRefts, ConstValue, FunType, Pred, Scalar};
use rustc::mir;
use rustc::ty::{Ty, TyCtxt};
pub use rustc_errors::ErrorReported;
use rustc_hir::BodyId;
use rustc_lint::{LateContext, LintContext};
use rustc_session::declare_lint;
use rustc_span::{MultiSpan, Span};
use std::collections::HashMap;
use std::iter;

declare_lint! {
    pub LIQUID_RUST,

    Forbid,
    "liquid rust"
}

pub struct LiquidRustCtxt<'a, 'tcx> {
    cx: &'a LateContext<'a, 'tcx>,
    refts_table: HashMap<BodyId, BodyRefts<'tcx>>,
}

impl<'a, 'tcx> LiquidRustCtxt<'a, 'tcx> {
    pub fn new(cx: &'a LateContext<'a, 'tcx>) -> Self {
        LiquidRustCtxt {
            cx,
            refts_table: HashMap::new(),
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.cx.tcx
    }

    pub fn hir(&self) -> &rustc::hir::map::Map<'tcx> {
        self.cx.tcx.hir()
    }

    pub fn track_errors<F, T>(&self, f: F) -> Result<T, ErrorReported>
    where
        F: FnOnce() -> T,
    {
        self.cx.sess().track_errors(f)
    }

    pub fn optimized_mir(&self, body_id: BodyId) -> &'tcx mir::Body<'tcx> {
        let def_id = self.hir().body_owner_def_id(body_id);
        self.cx.tcx.optimized_mir(def_id)
    }

    pub fn span_lint<S: Into<MultiSpan>>(&self, span: S, msg: &str) {
        self.cx.span_lint(LIQUID_RUST, span, msg);
    }

    pub fn span_lint_label(&self, span: Span, msg: &str) {
        let mut mspan = MultiSpan::from_span(span);
        mspan.push_span_label(span, msg.into());
        self.span_lint(mspan, msg);
    }

    pub fn abort_if_errors(&self) {
        self.cx.sess().abort_if_errors();
    }

    pub fn refine_true(&self) -> Pred<'tcx> {
        Pred::Constant(
            self.tcx().types.bool,
            ConstValue::Scalar(Scalar::from_bool(true)),
        )
    }

    pub fn mk_place_field(
        &self,
        place: refinements::Place<'tcx>,
        f: mir::Field,
        ty: Ty<'tcx>,
    ) -> Box<Pred<'tcx>> {
        self.mk_place_elem(place, mir::PlaceElem::Field(f, ty))
    }

    pub fn mk_place_elem(
        &self,
        place: refinements::Place<'tcx>,
        elem: mir::PlaceElem<'tcx>,
    ) -> Box<Pred<'tcx>> {
        let mut projection = place.projection.to_vec();
        projection.push(elem);

        box Pred::Place(refinements::Place {
            var: place.var,
            projection: self.tcx().intern_place_elems(&projection),
        })
    }

    pub fn add_body_refts(&mut self, body_refts: BodyRefts<'tcx>) {
        self.refts_table.insert(body_refts.body_id, body_refts);
    }

    pub fn local_decls(&self, body_id: BodyId) -> &HashMap<mir::Local, Pred<'tcx>> {
        if let Some(body_refts) = self.refts_table.get(&body_id) {
            &body_refts.local_decls
        } else {
            todo!()
        }
    }

    pub fn fun_type(&self, body_id: BodyId) -> FunType<'tcx> {
        if_chain! {
            if let Some(body_refts) = self.refts_table.get(&body_id);
            if let Some(fun_type) = &body_refts.fun_type;
            then {
                fun_type.clone()
            } else {
                let body = self.hir().body(body_id);
                let arg_count = body.params.len();
                let inputs = iter::repeat(self.refine_true()).take(arg_count).collect::<Vec<_>>();
                let output = self.refine_true();
                FunType {inputs, output}
            }
        }
    }

    // pub fn span_lint_note(&self, span: Span, msg: &str, note_span: Span, note: &str) {
    //     self.cx
    //         .span_lint_note(LIQUID_RUST, span, msg, note_span, note);
    // }

    // pub fn struct_span_lint<S: Into<MultiSpan>>(&self, span: S, msg: &str) -> DiagnosticBuilder {
    //     self.cx.struct_span_lint(LIQUID_RUST, span, msg)
    // }
}
