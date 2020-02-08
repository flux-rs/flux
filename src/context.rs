extern crate arena;
extern crate rustc_errors;
extern crate rustc_lint;
extern crate rustc_session;

use super::refinements::{self, ConstValue, Refine, Scalar};
use rustc::mir;
use rustc::ty::{Ty, TyCtxt};
pub use rustc_errors::ErrorReported;
use rustc_hir::BodyId;
use rustc_lint::{LateContext, LintContext};
use rustc_session::declare_lint;
use rustc_span::{MultiSpan, Span};

declare_lint! {
    pub LIQUID_RUST,

    Forbid,
    "liquid rust"
}

pub struct LiquidRustCtxt<'a, 'tcx> {
    cx: &'a LateContext<'a, 'tcx>,
}

impl<'a, 'tcx> LiquidRustCtxt<'a, 'tcx> {
    pub fn new(cx: &'a LateContext<'a, 'tcx>) -> Self {
        LiquidRustCtxt { cx }
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

    pub fn optimized_mir(&self, body_id: BodyId) -> &'tcx mir::BodyAndCache<'tcx> {
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

    pub fn refine_true(&self) -> Refine<'tcx> {
        Refine::Constant(
            self.tcx().types.bool,
            ConstValue::Scalar(Scalar::from_bool(true)),
        )
    }

    pub fn mk_place_field(
        &self,
        place: refinements::Place<'tcx>,
        f: mir::Field,
        ty: Ty<'tcx>,
    ) -> Box<Refine<'tcx>> {
        self.mk_place_elem(place, mir::PlaceElem::Field(f, ty))
    }

    pub fn mk_place_elem(
        &self,
        place: refinements::Place<'tcx>,
        elem: mir::PlaceElem<'tcx>,
    ) -> Box<Refine<'tcx>> {
        let mut projection = place.projection.to_vec();
        projection.push(elem);

        box Refine::Place(refinements::Place {
            var: place.var,
            projection: self.tcx().intern_place_elems(&projection),
        })
    }

    // pub fn span_lint_note(&self, span: Span, msg: &str, note_span: Span, note: &str) {
    //     self.cx
    //         .span_lint_note(LIQUID_RUST, span, msg, note_span, note);
    // }

    // pub fn struct_span_lint<S: Into<MultiSpan>>(&self, span: S, msg: &str) -> DiagnosticBuilder {
    //     self.cx.struct_span_lint(LIQUID_RUST, span, msg)
    // }
}
