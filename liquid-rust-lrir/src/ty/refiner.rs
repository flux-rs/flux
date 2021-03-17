use liquid_rust_common::index::IndexGen;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty as rs};
use rustc_mir::dataflow::move_paths::{LookupResult, MoveData, MovePathIndex};

use super::{BaseTy, Field, Kvar, Local, Ty, TyCtxt, Var};

pub struct RefinerCtxt<'a, 'tcx> {
    local: Local,
    vars_in_scope: &'a mut Vec<Var>,
    projection: Vec<mir::PlaceElem<'tcx>>,
    var_gen: &'a mut IndexGen,
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

pub trait TypeRefiner<'a, 'tcx>: Sized {
    fn tcx(&self) -> &TyCtxt;

    fn refine(
        &mut self,
        ty: rs::Ty<'tcx>,
        local: Local,
        var_gen: &'a mut IndexGen,
        vars_in_scope: &'a mut Vec<Var>,
    ) -> Ty {
        let mut cx = RefinerCtxt {
            local,
            var_gen,
            vars_in_scope,
            projection: vec![],
        };
        self.refine_with_cx(ty, &mut cx)
    }

    fn refine_with_cx(&mut self, ty: rs::Ty<'tcx>, cx: &mut RefinerCtxt<'a, 'tcx>) -> Ty {
        fold_ty(self, ty, cx)
    }

    fn refine_base_ty(&mut self, ty: BaseTy, cx: &mut RefinerCtxt<'a, 'tcx>) -> Ty {
        let kvar = Kvar {
            id: cx.var_gen.fresh(),
            vars: cx.vars_in_scope.clone(),
        };
        self.tcx().mk_refine(ty, kvar)
    }
}

pub struct MaybeUninitRefiner<'a, 'tcx> {
    tcx: &'a TyCtxt,
    move_data: &'a MoveData<'tcx>,
    maybe_uninit: &'a BitSet<MovePathIndex>,
}

impl<'a, 'tcx> MaybeUninitRefiner<'a, 'tcx> {
    pub fn new(
        tcx: &'a TyCtxt,
        move_data: &'a MoveData<'tcx>,
        maybe_uninit: &'a BitSet<MovePathIndex>,
    ) -> Self {
        Self {
            tcx,
            move_data,
            maybe_uninit,
        }
    }

    fn is_maybe_uninit(&self, local: mir::Local, projection: &[mir::PlaceElem<'tcx>]) -> bool {
        let place = mir::PlaceRef { local, projection };
        let move_path_index = match self.move_data.rev_lookup.find(place) {
            LookupResult::Exact(move_path_index) | LookupResult::Parent(Some(move_path_index)) => {
                move_path_index
            }
            LookupResult::Parent(None) => unreachable!(),
        };
        self.maybe_uninit.contains(move_path_index)
    }
}

impl<'a, 'tcx> TypeRefiner<'a, 'tcx> for MaybeUninitRefiner<'_, 'tcx> {
    fn refine_with_cx(&mut self, ty: rs::Ty<'tcx>, cx: &mut RefinerCtxt<'a, 'tcx>) -> Ty {
        // FIXME: if we are converting between locals maybe we should avoid having another
        // representation for the CFG.
        let local = mir::Local::from_usize(cx.local.as_usize());
        if self.is_maybe_uninit(local, &cx.projection) {
            return UninitRefiner::new(self.tcx).refine_with_cx(ty, cx);
        }
        fold_ty(self, ty, cx)
    }

    fn tcx(&self) -> &TyCtxt {
        self.tcx
    }
}

pub struct UninitRefiner<'a> {
    tcx: &'a TyCtxt,
}

impl<'a> UninitRefiner<'a> {
    pub fn new(tcx: &'a TyCtxt) -> Self {
        Self { tcx }
    }
}

impl<'a, 'tcx> TypeRefiner<'a, 'tcx> for UninitRefiner<'_> {
    fn refine_base_ty(&mut self, ty: BaseTy, _cx: &mut RefinerCtxt<'a, 'tcx>) -> Ty {
        self.tcx().mk_uninit(ty.size())
    }

    fn tcx(&self) -> &TyCtxt {
        self.tcx
    }
}

fn fold_ty<'a, 'tcx, R: TypeRefiner<'a, 'tcx>>(
    refiner: &mut R,
    ty: rs::Ty<'tcx>,
    cx: &mut RefinerCtxt<'a, 'tcx>,
) -> Ty {
    match ty.kind() {
        rs::TyKind::Tuple(_) => {
            let tup = ty
                .tuple_fields()
                .enumerate()
                .map(|(i, ty)| {
                    let fld = Field::from_usize(i);
                    cx.push_field(i, ty);
                    let ty = fold_ty(refiner, ty, cx);
                    cx.pop_field();
                    (fld, ty)
                })
                .collect();
            refiner.tcx().mk_tuple(tup)
        }
        rs::TyKind::Bool => refiner.refine_base_ty(BaseTy::Bool, cx),
        rs::TyKind::Int(_) | rs::TyKind::Uint(_) => refiner.refine_base_ty(BaseTy::Int, cx),
        rs::TyKind::Ref(..) => todo!(),
        _ => todo!(),
    }
}
