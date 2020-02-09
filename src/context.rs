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
    pub reft_true: &'a Pred<'a, 'tcx>,
    pub nu: &'a Pred<'a, 'tcx>,
}

impl<'a, 'tcx> LiquidRustCtxt<'a, 'tcx> {
    pub fn new(cx: &'a LateContext<'a, 'tcx>, preds: &'a ArenaInterner<Pred<'a, 'tcx>>) -> Self {
        let reft_true = Pred::Constant(
            cx.tcx.types.bool,
            ConstValue::Scalar(Scalar::from_bool(true)),
        );

        LiquidRustCtxt {
            cx,
            refts_table: HashMap::new(),
            preds,
            reft_true: preds.intern(reft_true),
            nu: preds.intern(Pred::nu()),
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

    pub fn mk_fun_type(
        &self,
        inputs: &[Pred<'a, 'tcx>],
        output: &'a Pred<'a, 'tcx>,
    ) -> FunType<'a, 'tcx> {
        let inputs = self.preds.alloc_slice(inputs);
        FunType { inputs, output }
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

    pub fn local_decls(&self, body_id: BodyId) -> &HashMap<mir::Local, &'a Pred<'a, 'tcx>> {
        let def_id = self.hir().body_owner_def_id(body_id);
        if let Some(body_refts) = self.refts_table.get(&def_id) {
            &body_refts.local_decls
        } else {
            todo!()
        }
    }

    pub fn fun_type(&self, def_id: DefId) -> FunType<'a, 'tcx> {
        if_chain! {
            if let Some(body_refts) = self.refts_table.get(&def_id);
            if let Some(fun_type) = body_refts.fun_type;
            then {
                fun_type
            } else {
                let arg_count = self.tcx().fn_sig(def_id).skip_binder().inputs().len();
                let inputs = self.preds.alloc_from_iter(iter::repeat(*self.reft_true).take(arg_count));
                let output = self.reft_true;
                FunType { inputs, output }
            }
        }
    }

    pub fn open_pred_with_locals(
        &self,
        pred: &'a Pred<'a, 'tcx>,
        locals: &[mir::Local],
    ) -> &'a Pred<'a, 'tcx> {
        self.open_pred(pred, &Value::from_locals(locals))
    }

    pub fn open_fun_type_with_locals(
        &self,
        fun_type: FunType<'a, 'tcx>,
        locals: &[mir::Local],
    ) -> Vec<&'a Pred<'a, 'tcx>> {
        self.open_fun_type(fun_type, &Value::from_locals(locals))
    }

    pub fn open_pred(
        &self,
        pred: &'a Pred<'a, 'tcx>,
        values: &[Value<'tcx>],
    ) -> &'a Pred<'a, 'tcx> {
        match pred {
            Pred::Unary(op, pred) => self.mk_unary(*op, self.open_pred(pred, values)),
            Pred::Binary(lhs, op, rhs) => self.mk_binary(
                self.open_pred(lhs, values),
                *op,
                self.open_pred(rhs, values),
            ),
            Pred::Place(place) => match place.var {
                Var::Free(_) => pred,
                Var::Bound(idx) => match values[values.len() - idx - 1] {
                    Value::Constant(ty, val) => self.mk_constant(ty, val),
                    Value::Local(local) => self.mk_pred_place(Place {
                        var: Var::Free(local),
                        projection: place.projection,
                    }),
                },
            },
            Pred::Constant(..) => pred,
        }
    }

    pub fn open_fun_type(
        &self,
        fun_type: FunType<'a, 'tcx>,
        inputs_and_output: &[Value<'tcx>],
    ) -> Vec<&'a Pred<'a, 'tcx>> {
        assert_eq!(inputs_and_output.len(), fun_type.inputs.len() + 1);
        let mut refines = fun_type
            .inputs
            .iter()
            .enumerate()
            .map(|(i, pred)| self.open_pred(pred, &inputs_and_output[0..i + 1]))
            .collect::<Vec<_>>();
        refines.push(self.open_pred(fun_type.output, inputs_and_output));
        refines
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
