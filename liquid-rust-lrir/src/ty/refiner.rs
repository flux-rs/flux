use liquid_rust_common::index::IndexGen;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty as rs};
use rustc_mir_dataflow::move_paths::{LookupResult, MoveData, MovePathIndex};

use super::{BaseTy, Field, KVid, Kvar, Local, Ty, TyCtxt, Var};

pub struct Refiner<'a, 'tcx> {
    tcx: &'a TyCtxt,
    move_data: &'a MoveData<'tcx>,
    maybe_uninit: &'a BitSet<MovePathIndex>,
    kvid_gen: &'a IndexGen<KVid>,
}

impl<'a, 'tcx> Refiner<'a, 'tcx> {
    pub fn new(
        tcx: &'a TyCtxt,
        move_data: &'a MoveData<'tcx>,
        maybe_uninit: &'a BitSet<MovePathIndex>,
        kvid_gen: &'a IndexGen<KVid>,
    ) -> Self {
        Self {
            tcx,
            move_data,
            maybe_uninit,
            kvid_gen,
        }
    }

    pub fn maybe_uninit(
        &mut self,
        ty: rs::Ty<'tcx>,
        local: Local,
        vars_in_scope: &mut Vec<Var>,
    ) -> Ty {
        let mut cx = RefinerCtxt {
            local,
            vars_in_scope,
            projection: vec![],
        };
        self.maybe_uninit_with_cx(ty, &mut cx)
    }

    fn maybe_uninit_with_cx(&mut self, ty: rs::Ty<'tcx>, cx: &mut RefinerCtxt<'_, 'tcx>) -> Ty {
        if self.is_maybe_uninit(cx) {
            return Refiner::uninit(self.tcx, ty);
        }

        let tcx = self.tcx;
        match ty.kind() {
            rs::TyKind::Tuple(_) => {
                let tup = ty
                    .tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| {
                        let fld = Field::from_usize(i);
                        cx.push_field(i, ty);
                        let ty = self.maybe_uninit_with_cx(ty, cx);
                        cx.pop_field();
                        (fld, ty)
                    })
                    .collect();
                self.tcx.mk_tuple(tup)
            }
            rs::TyKind::Bool => tcx.mk_refine(BaseTy::Bool, self.fresh_kvar(cx)),
            rs::TyKind::Int(_) | rs::TyKind::Uint(_) => {
                tcx.mk_refine(BaseTy::Int, self.fresh_kvar(cx))
            }
            rs::TyKind::Ref(..) => todo!(),
            _ => todo!(),
        }
    }

    pub fn uninit(tcx: &TyCtxt, ty: rs::Ty) -> Ty {
        match ty.kind() {
            rs::TyKind::Tuple(_) => {
                let tup = ty
                    .tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| (Field::from_usize(i), Refiner::uninit(tcx, ty)))
                    .collect();
                tcx.mk_tuple(tup)
            }
            // FIXME: use actual sizes
            rs::TyKind::Ref(..) | rs::TyKind::Bool | rs::TyKind::Int(_) | rs::TyKind::Uint(_) => {
                tcx.mk_uninit(1)
            }
            _ => todo!(),
        }
    }

    fn fresh_kvar(&self, cx: &mut RefinerCtxt<'_, 'tcx>) -> Kvar {
        // Fixpoint requires the first argument of kvar to be Nu
        let mut vars = vec![Var::Nu];
        vars.extend(cx.vars_in_scope.iter());
        Kvar {
            id: self.kvid_gen.fresh(),
            vars,
        }
    }

    fn is_maybe_uninit(&self, cx: &mut RefinerCtxt<'_, 'tcx>) -> bool {
        let local = mir::Local::from_usize(cx.local.as_usize());
        let place = mir::PlaceRef {
            local,
            projection: &cx.projection,
        };
        let move_path_index = match self.move_data.rev_lookup.find(place) {
            LookupResult::Exact(move_path_index) | LookupResult::Parent(Some(move_path_index)) => {
                move_path_index
            }
            LookupResult::Parent(None) => unreachable!(),
        };
        self.maybe_uninit.contains(move_path_index)
    }
}

struct RefinerCtxt<'a, 'tcx> {
    local: Local,
    vars_in_scope: &'a mut Vec<Var>,
    projection: Vec<mir::PlaceElem<'tcx>>,
}

impl<'a, 'tcx> RefinerCtxt<'a, 'tcx> {
    fn push_field(&mut self, i: usize, ty: rs::Ty<'tcx>) {
        self.vars_in_scope.push(Field::from_usize(i).into());
        self.projection
            .push(mir::PlaceElem::Field(mir::Field::from_usize(i), ty));
    }

    fn pop_field(&mut self) {
        self.vars_in_scope.pop();
        self.projection.pop();
    }
}
