extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_lint;
extern crate rustc_session;

use super::refinements::*;
use super::syntax::ast;
use arena::TypedArena;
use rustc_data_structures::sharded::ShardedHashMap;
pub use rustc_errors::ErrorReported;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    BodyId,
};
use rustc_lint::{LateContext, LintContext};
use rustc_middle::mir;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_session::declare_lint;
use rustc_span::{MultiSpan, Span};
use std::collections::HashMap;
use std::hash::Hash;

declare_lint! {
    pub LIQUID_RUST,

    Forbid,
    "liquid rust"
}

pub struct LiquidRustCtxt<'lr, 'tcx> {
    cx: &'lr LateContext<'lr, 'tcx>,
    refts_table: HashMap<LocalDefId, BodyRefts<'lr, 'tcx>>,
    preds: &'lr ArenaInterner<'lr, Pred<'lr, 'tcx>>,
    refts: &'lr ArenaInterner<'lr, ReftType<'lr, 'tcx>>,
    pub pred_true: &'lr Pred<'lr, 'tcx>,
    pub pred_false: &'lr Pred<'lr, 'tcx>,
    pub nu: &'lr Pred<'lr, 'tcx>,
}

impl<'lr, 'tcx> LiquidRustCtxt<'lr, 'tcx> {
    pub fn new(
        cx: &'lr LateContext<'lr, 'tcx>,
        preds: &'lr ArenaInterner<Pred<'lr, 'tcx>>,
        refts: &'lr ArenaInterner<ReftType<'lr, 'tcx>>,
    ) -> Self {
        let pred_true = preds.intern(Pred::Operand(Operand::Constant(
            cx.tcx.types.bool,
            Scalar::from_bool(true),
        )));
        let pred_false = preds.intern(Pred::Operand(Operand::Constant(
            cx.tcx.types.bool,
            Scalar::from_bool(false),
        )));

        LiquidRustCtxt {
            cx,
            refts_table: HashMap::new(),
            preds,
            pred_true,
            pred_false,
            nu: preds.intern(Pred::nu()),
            refts,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.cx.tcx
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
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
        self.cx.struct_span_lint(LIQUID_RUST, span, |ldb| {
            ldb.build(msg).emit();
        });
    }

    pub fn span_lint_label(&self, span: Span, msg: &str) {
        let mut mspan = MultiSpan::from_span(span);
        mspan.push_span_label(span, msg.into());
        self.span_lint(mspan, msg);
    }

    pub fn abort_if_errors(&self) {
        self.cx.sess().abort_if_errors();
    }

    pub fn mk_reft(&self, ty: Ty<'tcx>, pred: &'lr Pred<'lr, 'tcx>) -> &'lr ReftType<'lr, 'tcx> {
        self.refts.intern(ReftType::Reft(ty, pred))
    }

    pub fn mk_fun_type(
        &self,
        inputs: Vec<&'lr ReftType<'lr, 'tcx>>,
        output: &'lr ReftType<'lr, 'tcx>,
    ) -> &'lr ReftType<'lr, 'tcx> {
        let inputs = self.refts.alloc_from_iter(inputs.into_iter().map(|p| *p));
        self.refts.intern(ReftType::Fun { inputs, output })
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

    pub fn mk_true(&self, ty: Ty<'tcx>) -> &'lr ReftType<'lr, 'tcx> {
        self.mk_reft(ty, self.pred_true)
    }

    pub fn mk_operand(&self, operand: Operand<'tcx>) -> &'lr Pred<'lr, 'tcx> {
        self.preds.intern(Pred::Operand(operand))
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
            if let Some(local_def_id) = def_id.as_local();
            if let Some(body_refts) = self.refts_table.get(&local_def_id);
            if let Some(fun_type) = body_refts.fun_type;
            then {
                fun_type
            } else {
                let fn_sig = self.tcx().fn_sig(def_id);
                let fn_sig = fn_sig.skip_binder();
                let inputs = fn_sig.inputs().iter().map(|ty| *self.mk_true(ty));
                let inputs = self.refts.alloc_from_iter(inputs);
                let output = self.mk_true(fn_sig.output());
                Binder::bind(self.refts.intern(ReftType::Fun { inputs, output}))
            }
        }
    }

    pub fn open_pred(
        &self,
        pred: Binder<&'lr Pred<'lr, 'tcx>>,
        value: Operand<'tcx>,
    ) -> &'lr Pred<'lr, 'tcx> {
        self._open_pred(pred.skip_binder(), &[value], 1)
    }

    fn _open_pred(
        &self,
        pred: &'lr Pred<'lr, 'tcx>,
        values: &[Operand<'tcx>],
        nbinders: usize,
    ) -> &'lr Pred<'lr, 'tcx> {
        match pred {
            Pred::Unary(op, pred) => self.mk_unary(*op, self._open_pred(pred, values, nbinders)),
            Pred::Binary(lhs, op, rhs) => self.mk_binary(
                self._open_pred(lhs, values, nbinders),
                *op,
                self._open_pred(rhs, values, nbinders),
            ),
            Pred::Operand(operand) => {
                self.mk_operand(self._open_operand(*operand, values, nbinders))
            }
        }
    }

    fn _open_operand(
        &self,
        operand: Operand<'tcx>,
        values: &[Operand<'tcx>],
        nbinders: usize,
    ) -> Operand<'tcx> {
        match operand {
            Operand::Place(place) => match place.var {
                Var::Bound(idx) if values.len() + idx >= nbinders => {
                    match values[nbinders - idx - 1] {
                        c @ Operand::Constant(..) => {
                            if place.projection.len() > 0 {
                                bug!("cannot replace a constant into a projected place");
                            }
                            c
                        }
                        Operand::Place(Place { var, projection }) => {
                            let mut projection = projection.to_vec();
                            projection.extend(place.projection);

                            Operand::Place(Place {
                                var,
                                projection: self.tcx().intern_place_elems(&projection),
                            })
                        }
                    }
                }
                _ => operand,
            },
            Operand::Constant(..) => operand,
        }
    }

    pub fn split_fun_type(
        &self,
        reft_type: Binder<&'lr ReftType<'lr, 'tcx>>,
        values: &[Operand<'tcx>],
    ) -> (
        Vec<Binder<&'lr ReftType<'lr, 'tcx>>>,
        Binder<&'lr ReftType<'lr, 'tcx>>,
    ) {
        match reft_type.skip_binder() {
            ReftType::Reft(..) => bug!("expected function type"),
            ReftType::Fun { inputs, output } => {
                let inputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(i, reft_ty)| {
                        Binder::bind(self._open_reft_type(reft_ty, &values[0..i], i))
                    })
                    .collect::<Vec<_>>();
                let output = Binder::bind(self._open_reft_type(output, values, inputs.len()));
                (inputs, output)
            }
        }
    }

    fn _open_reft_type(
        &self,
        reft_type: &'lr ReftType<'lr, 'tcx>,
        values: &[Operand<'tcx>],
        nbinders: usize,
    ) -> &'lr ReftType<'lr, 'tcx> {
        self.fold_reft_type(reft_type, nbinders, &|pred, nbinders| {
            self._open_pred(pred, values, nbinders)
        })
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
            Pred::Operand(operand) => {
                self.mk_operand(self.open_operand_with_fresh_vars(*operand, nbinders))
            }
        }
    }

    fn open_operand_with_fresh_vars(
        &self,
        operand: Operand<'tcx>,
        nbinders: usize,
    ) -> Operand<'tcx> {
        match operand {
            Operand::Place(place) => match place.var {
                Var::Bound(idx) => Operand::Place(Place {
                    var: Var::Free(nbinders - idx - 1),
                    projection: place.projection,
                }),
                _ => operand,
            },
            Operand::Constant(..) => operand,
        }
    }

    pub fn open_with_fresh_vars(
        &self,
        reft_type: Binder<&'lr ReftType<'lr, 'tcx>>,
    ) -> &'lr ReftType<'lr, 'tcx> {
        self.fold_reft_type(reft_type.skip_binder(), 0, &|pred, nbinders| {
            self.open_pred_with_fresh_vars(pred, nbinders)
        })
    }

    fn fold_reft_type(
        &self,
        reft_type: &'lr ReftType<'lr, 'tcx>,
        nbinders: usize,
        pred_folder: &impl Fn(&'lr Pred<'lr, 'tcx>, usize) -> &'lr Pred<'lr, 'tcx>,
    ) -> &'lr ReftType<'lr, 'tcx> {
        match reft_type {
            ReftType::Reft(ty, pred) => self.mk_reft(ty, pred_folder(pred, nbinders + 1)),
            ReftType::Fun { inputs, output } => {
                let inputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(i, reft_type)| self.fold_reft_type(reft_type, nbinders + i, pred_folder))
                    .collect::<Vec<_>>();
                let output = self.fold_reft_type(output, inputs.len() + nbinders, pred_folder);
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
