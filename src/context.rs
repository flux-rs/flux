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

pub struct LiquidRustCtxt<'a, 'tcx> {
    cx: &'a LateContext<'a, 'tcx>,
    refts_table: HashMap<DefId, BodyRefts<'a, 'tcx>>,
    preds: &'a ArenaInterner<'a, Pred<'a, 'tcx>>,
    refts: &'a ArenaInterner<'a, ReftType<'a, 'tcx>>,
    pub reft_true: &'a ReftType<'a, 'tcx>,
    pub nu: &'a Pred<'a, 'tcx>,
}

impl<'a, 'tcx> LiquidRustCtxt<'a, 'tcx> {
    pub fn new(
        cx: &'a LateContext<'a, 'tcx>,
        preds: &'a ArenaInterner<Pred<'a, 'tcx>>,
        refts: &'a ArenaInterner<ReftType<'a, 'tcx>>,
    ) -> Self {
        let pred_true = Pred::Constant(
            cx.tcx.types.bool,
            ConstValue::Scalar(Scalar::from_bool(true)),
        );

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

    pub fn mk_reft(&self, pred: &'a Pred<'a, 'tcx>) -> &'a ReftType<'a, 'tcx> {
        self.refts.intern(ReftType::Reft(pred))
    }

    pub fn mk_fun_type(
        &self,
        inputs: Vec<&'a ReftType<'a, 'tcx>>,
        output: &'a ReftType<'a, 'tcx>,
    ) -> &'a ReftType<'a, 'tcx> {
        let inputs = self.refts.alloc_from_iter(inputs.into_iter().map(|p| *p));
        self.refts.intern(ReftType::Fun { inputs, output })
    }

    pub fn mk_place_var(&self, var: Var) -> &'a Pred<'a, 'tcx> {
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

    pub fn mk_pred_place(&self, place: Place<'tcx>) -> &'a Pred<'a, 'tcx> {
        self.preds.intern(Pred::Place(place))
    }

    pub fn mk_constant(&self, ty: Ty<'tcx>, val: ConstValue<'tcx>) -> &'a Pred<'a, 'tcx> {
        self.preds.intern(Pred::Constant(ty, val))
    }

    pub fn mk_binary(
        &self,
        lhs: &'a Pred<'a, 'tcx>,
        op: ast::BinOpKind,
        rhs: &'a Pred<'a, 'tcx>,
    ) -> &'a Pred<'a, 'tcx> {
        self.preds.intern(Pred::Binary(lhs, op, rhs))
    }

    pub fn mk_unary(&self, op: ast::UnOpKind, pred: &'a Pred<'a, 'tcx>) -> &'a Pred<'a, 'tcx> {
        self.preds.intern(Pred::Unary(op, pred))
    }

    pub fn add_body_refts(&mut self, body_refts: BodyRefts<'a, 'tcx>) {
        let def_id = self.hir().body_owner_def_id(body_refts.body_id);
        self.refts_table.insert(def_id, body_refts);
    }

    pub fn local_decls(&self, body_id: BodyId) -> &HashMap<mir::Local, &'a ReftType<'a, 'tcx>> {
        let def_id = self.hir().body_owner_def_id(body_id);
        if let Some(body_refts) = self.refts_table.get(&def_id) {
            &body_refts.local_decls
        } else {
            todo!()
        }
    }

    pub fn reft_type_for(&self, def_id: DefId) -> &'a ReftType<'a, 'tcx> {
        if_chain! {
            if let Some(body_refts) = self.refts_table.get(&def_id);
            if let Some(fun_type) = body_refts.fun_type;
            then {
                fun_type
            } else {
                let arg_count = self.tcx().fn_sig(def_id).skip_binder().inputs().len();
                let inputs = self.refts.alloc_from_iter(iter::repeat(*self.reft_true).take(arg_count));
                let output = self.reft_true;
                self.refts.intern(ReftType::Fun { inputs, output})
            }
        }
    }

    pub fn open_pred(
        &self,
        pred: &'a Pred<'a, 'tcx>,
        values: &[Value<'tcx>],
        keep_inner_most: bool,
    ) -> &'a Pred<'a, 'tcx> {
        match pred {
            Pred::Unary(op, pred) => {
                self.mk_unary(*op, self.open_pred(pred, values, keep_inner_most))
            }
            Pred::Binary(lhs, op, rhs) => self.mk_binary(
                self.open_pred(lhs, values, keep_inner_most),
                *op,
                self.open_pred(rhs, values, keep_inner_most),
            ),
            Pred::Place(place) => match place.var {
                Var::Bound(idx) => {
                    if idx == 0 && keep_inner_most {
                        return pred;
                    }
                    match values[values.len() - idx - 1] {
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

    pub fn open_reft_type(
        &self,
        reft_type: &'a ReftType<'a, 'tcx>,
        values: &[Value<'tcx>],
    ) -> Vec<&'a ReftType<'a, 'tcx>> {
        match reft_type {
            ReftType::Reft(pred) => vec![self.mk_reft(self.open_pred(pred, values, true))],
            ReftType::Fun { inputs, output } => {
                let mut refts = inputs
                    .iter()
                    .enumerate()
                    .flat_map(|(i, reft_ty)| self.open_reft_type(reft_ty, &values[0..i + 1]))
                    .collect::<Vec<_>>();
                refts.extend(self.open_reft_type(output, values));
                refts
            }
        }
    }

    fn open_pred_with_fresh_vars(&self, pred: &'a Pred<'a, 'tcx>, n: usize) -> &'a Pred<'a, 'tcx> {
        match pred {
            Pred::Unary(op, pred) => self.mk_unary(*op, self.open_pred_with_fresh_vars(pred, n)),
            Pred::Binary(lhs, op, rhs) => self.mk_binary(
                self.open_pred_with_fresh_vars(lhs, n),
                *op,
                self.open_pred_with_fresh_vars(rhs, n),
            ),
            Pred::Place(place) => match place.var {
                Var::Bound(idx) => self.mk_pred_place(Place {
                    var: Var::Free(n - idx - 1),
                    projection: place.projection,
                }),
                _ => pred,
            },
            Pred::Constant(..) => pred,
        }
    }

    pub fn open_with_fresh_vars(
        &self,
        reft_type: &'a ReftType<'a, 'tcx>,
    ) -> &'a ReftType<'a, 'tcx> {
        self._open_with_fresh_vars(reft_type, 0)
    }

    fn _open_with_fresh_vars(
        &self,
        reft_type: &'a ReftType<'a, 'tcx>,
        n: usize,
    ) -> &'a ReftType<'a, 'tcx> {
        match reft_type {
            ReftType::Reft(pred) => self.mk_reft(self.open_pred_with_fresh_vars(pred, n + 1)),
            ReftType::Fun { inputs, output } => {
                let output = self._open_with_fresh_vars(output, inputs.len() + n);
                let inputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(i, reft_type)| self._open_with_fresh_vars(reft_type, n + i))
                    .collect::<Vec<_>>();
                self.mk_fun_type(inputs, output)
            }
        }
    }
}

pub struct ArenaInterner<'a, T: 'a> {
    arena: &'a TypedArena<T>,
    interner: ShardedHashMap<&'a T, ()>,
}

impl<'a, T: Hash + Eq + Copy> ArenaInterner<'a, T> {
    pub fn new(arena: &'a TypedArena<T>) -> Self {
        ArenaInterner {
            arena,
            interner: ShardedHashMap::default(),
        }
    }

    pub fn intern(&self, pred: T) -> &'a T {
        self.interner.intern(pred, |pred| self.arena.alloc(pred))
    }

    pub fn alloc_slice(&self, slice: &[T]) -> &'a [T] {
        self.arena.alloc_slice(slice)
    }

    pub fn alloc_from_iter<I: IntoIterator<Item = T>>(&self, iter: I) -> &'a mut [T] {
        self.arena.alloc_from_iter(iter)
    }
}
