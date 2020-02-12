extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_lint;
extern crate rustc_session;

use super::refinements::*;
use super::syntax::ast;
use arena::TypedArena;
use rustc::mir;
use rustc::ty::{Ty, TyCtxt};
use rustc_data_structures::sharded::ShardedHashMap;
pub use rustc_errors::ErrorReported;
use rustc_hir::{def_id::DefId, BodyId};
use rustc_lint::{LateContext, LintContext};
use rustc_session::declare_lint;
use rustc_span::{MultiSpan, Span};
use std::collections::HashMap;
use std::hash::Hash;
use std::iter;

declare_lint! {
    pub LIQUID_RUST,

    Forbid,
    "liquid rust"
}

pub struct LiquidRustCtxt<'lr, 'tcx> {
    cx: &'lr LateContext<'lr, 'tcx>,
    refts_table: HashMap<DefId, BodyRefts<'lr, 'tcx>>,
    preds: &'lr ArenaInterner<'lr, Pred<'lr, 'tcx>>,
    refts: &'lr ArenaInterner<'lr, ReftType<'lr, 'tcx>>,
    pub reft_true: &'lr ReftType<'lr, 'tcx>,
    pub nu: &'lr Pred<'lr, 'tcx>,
}

impl<'lr, 'tcx> LiquidRustCtxt<'lr, 'tcx> {
    pub fn new(
        cx: &'lr LateContext<'lr, 'tcx>,
        preds: &'lr ArenaInterner<Pred<'lr, 'tcx>>,
        refts: &'lr ArenaInterner<ReftType<'lr, 'tcx>>,
    ) -> Self {
        let pred_true = Pred::Constant(cx.tcx.types.bool, Scalar::from_bool(true));

        LiquidRustCtxt {
            cx,
            refts_table: HashMap::new(),
            preds,
            reft_true: refts.intern(ReftType::Reft(preds.intern(pred_true))),
            nu: preds.intern(Pred::nu()),
            refts,
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

    pub fn mk_reft(&self, pred: &'lr Pred<'lr, 'tcx>) -> &'lr ReftType<'lr, 'tcx> {
        self.refts.intern(ReftType::Reft(pred))
    }

    pub fn mk_fun_type(
        &self,
        inputs: Vec<&'lr ReftType<'lr, 'tcx>>,
        output: &'lr ReftType<'lr, 'tcx>,
    ) -> &'lr ReftType<'lr, 'tcx> {
        let inputs = self.refts.alloc_from_iter(inputs.into_iter().map(|p| *p));
        self.refts.intern(ReftType::Fun { inputs, output })
    }

    pub fn mk_place_var(&self, var: Var) -> &'lr Pred<'lr, 'tcx> {
        self.preds.intern(Pred::Place(Place::from_var(var)))
    }

    pub fn mk_place_field(&self, place: Place<'tcx>, f: mir::Field, ty: Ty<'tcx>) -> Place<'tcx> {
        self.mk_place_elem(place, mir::PlaceElem::Field(f, ty))
    }

    pub fn mk_place_elem(&self, place: Place<'tcx>, elem: mir::PlaceElem<'tcx>) -> Place<'tcx> {
        let mut projection = place.projection.to_vec();
        projection.push(elem);

        Place {
            var: place.var,
            projection: self.tcx().intern_place_elems(&projection),
        }
    }

    pub fn mk_pred_place(&self, place: Place<'tcx>) -> &'lr Pred<'lr, 'tcx> {
        self.preds.intern(Pred::Place(place))
    }

    pub fn mk_constant(&self, ty: Ty<'tcx>, scalar: Scalar) -> &'lr Pred<'lr, 'tcx> {
        self.preds.intern(Pred::Constant(ty, scalar))
    }

    pub fn mk_binary(
        &self,
        lhs: &'lr Pred<'lr, 'tcx>,
        op: ast::BinOpKind,
        rhs: &'lr Pred<'lr, 'tcx>,
    ) -> &'lr Pred<'lr, 'tcx> {
        self.preds.intern(Pred::Binary(lhs, op, rhs))
    }

    pub fn mk_unary(&self, op: ast::UnOpKind, pred: &'lr Pred<'lr, 'tcx>) -> &'lr Pred<'lr, 'tcx> {
        self.preds.intern(Pred::Unary(op, pred))
    }

    pub fn add_body_refts(&mut self, body_refts: BodyRefts<'lr, 'tcx>) {
        let def_id = self.hir().body_owner_def_id(body_refts.body_id);
        self.refts_table.insert(def_id, body_refts);
    }

    pub fn local_decls(
        &self,
        body_id: BodyId,
    ) -> &HashMap<mir::Local, Binder<&'lr ReftType<'lr, 'tcx>>> {
        let def_id = self.hir().body_owner_def_id(body_id);
        if let Some(body_refts) = self.refts_table.get(&def_id) {
            &body_refts.local_decls
        } else {
            todo!()
        }
    }

    pub fn reft_type_for(&self, def_id: DefId) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        if_chain! {
            if let Some(body_refts) = self.refts_table.get(&def_id);
            if let Some(fun_type) = body_refts.fun_type;
            then {
                fun_type
            } else {
                let arg_count = self.tcx().fn_sig(def_id).skip_binder().inputs().len();
                let inputs = self.refts.alloc_from_iter(iter::repeat(*self.reft_true).take(arg_count));
                let output = self.reft_true;
                Binder::bind(self.refts.intern(ReftType::Fun { inputs, output}))
            }
        }
    }

    pub fn open_pred(
        &self,
        pred: Binder<&'lr Pred<'lr, 'tcx>>,
        value: Value<'tcx>,
    ) -> &'lr Pred<'lr, 'tcx> {
        self._open_pred(pred.skip_binder(), &[value], 1)
    }

    fn _open_pred(
        &self,
        pred: &'lr Pred<'lr, 'tcx>,
        values: &[Value<'tcx>],
        nbinders: usize,
    ) -> &'lr Pred<'lr, 'tcx> {
        match pred {
            Pred::Unary(op, pred) => self.mk_unary(*op, self._open_pred(pred, values, nbinders)),
            Pred::Binary(lhs, op, rhs) => self.mk_binary(
                self._open_pred(lhs, values, nbinders),
                *op,
                self._open_pred(rhs, values, nbinders),
            ),
            Pred::Place(place) => match place.var {
                Var::Bound(idx) if values.len() + idx >= nbinders => {
                    match values[nbinders - idx - 1] {
                        Value::Constant(ty, val) => self.mk_constant(ty, val),
                        Value::Local(local) => self.mk_pred_place(Place {
                            var: Var::Local(local),
                            projection: place.projection,
                        }),
                    }
                }
                _ => pred,
            },
            Pred::Constant(..) => pred,
        }
    }

    pub fn open_fun_type(
        &self,
        reft_type: Binder<&'lr ReftType<'lr, 'tcx>>,
        values: &[Value<'tcx>],
    ) -> (
        Vec<Binder<&'lr ReftType<'lr, 'tcx>>>,
        Binder<&'lr ReftType<'lr, 'tcx>>,
    ) {
        match reft_type.skip_binder() {
            ReftType::Reft(..) => bug!("expected function type"),
            ReftType::Fun { inputs, output } => {
                let output = Binder::bind(self._open_reft_type(output, values, inputs.len()));
                let inputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(i, reft_ty)| {
                        Binder::bind(self._open_reft_type(reft_ty, &values[0..i], i))
                    })
                    .collect::<Vec<_>>();
                (inputs, output)
            }
        }
    }

    fn _open_reft_type(
        &self,
        reft_type: &'lr ReftType<'lr, 'tcx>,
        values: &[Value<'tcx>],
        nbinders: usize,
    ) -> &'lr ReftType<'lr, 'tcx> {
        match reft_type {
            ReftType::Reft(pred) => self.mk_reft(self._open_pred(pred, values, nbinders + 1)),
            ReftType::Fun { inputs, output } => {
                let output = self._open_reft_type(output, values, nbinders + inputs.len());
                let inputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(i, reft_ty)| self._open_reft_type(reft_ty, values, nbinders + i))
                    .collect::<Vec<_>>();
                self.mk_fun_type(inputs, output)
            }
        }
    }

    fn open_pred_with_fresh_vars(
        &self,
        pred: &'lr Pred<'lr, 'tcx>,
        nbinders: usize,
    ) -> &'lr Pred<'lr, 'tcx> {
        match pred {
            Pred::Unary(op, pred) => {
                self.mk_unary(*op, self.open_pred_with_fresh_vars(pred, nbinders))
            }
            Pred::Binary(lhs, op, rhs) => self.mk_binary(
                self.open_pred_with_fresh_vars(lhs, nbinders),
                *op,
                self.open_pred_with_fresh_vars(rhs, nbinders),
            ),
            Pred::Place(place) => match place.var {
                Var::Bound(idx) => self.mk_pred_place(Place {
                    var: Var::Free(nbinders - idx - 1),
                    projection: place.projection,
                }),
                _ => pred,
            },
            Pred::Constant(..) => pred,
        }
    }

    pub fn open_with_fresh_vars(
        &self,
        reft_type: Binder<&'lr ReftType<'lr, 'tcx>>,
    ) -> &'lr ReftType<'lr, 'tcx> {
        self._open_with_fresh_vars(reft_type.skip_binder(), 0)
    }

    fn _open_with_fresh_vars(
        &self,
        reft_type: &'lr ReftType<'lr, 'tcx>,
        nbinders: usize,
    ) -> &'lr ReftType<'lr, 'tcx> {
        match reft_type {
            ReftType::Reft(pred) => {
                self.mk_reft(self.open_pred_with_fresh_vars(pred, nbinders + 1))
            }
            ReftType::Fun { inputs, output } => {
                let output = self._open_with_fresh_vars(output, inputs.len() + nbinders);
                let inputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(i, reft_type)| self._open_with_fresh_vars(reft_type, nbinders + i))
                    .collect::<Vec<_>>();
                self.mk_fun_type(inputs, output)
            }
        }
    }
}

pub struct ArenaInterner<'a, T> {
    arena: TypedArena<T>,
    interner: ShardedHashMap<&'a T, ()>,
}

impl<'a, T: Hash + Eq + Copy> ArenaInterner<'a, T> {
    pub fn new(arena: TypedArena<T>) -> Self {
        ArenaInterner {
            arena,
            interner: ShardedHashMap::default(),
        }
    }

    pub fn intern<'b>(&'a self, pred: T) -> &'a T {
        self.interner.intern(pred, |pred| self.arena.alloc(pred))
    }

    pub fn alloc_slice(&'a self, slice: &[T]) -> &'a [T] {
        self.arena.alloc_slice(slice)
    }

    pub fn alloc_from_iter<I: IntoIterator<Item = T>>(&'a self, iter: I) -> &'a mut [T] {
        self.arena.alloc_from_iter(iter)
    }
}
