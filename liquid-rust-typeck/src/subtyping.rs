use itertools::izip;
use rustc_middle::ty::TyCtxt;

use crate::{
    pure_ctxt::Cursor,
    ty::{BaseTy, BinOp, ExprKind, Ty, TyKind, Var},
};

pub struct Sub<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    cursor: Cursor<'a>,
}

impl Sub<'_, '_> {
    pub fn new<'a, 'tcx>(tcx: TyCtxt<'tcx>, cursor: Cursor<'a>) -> Sub<'a, 'tcx> {
        Sub { tcx, cursor }
    }

    pub fn subtyping(&mut self, ty1: Ty, ty2: Ty) {
        let sub = &mut Sub::new(self.tcx, self.cursor.breadcrumb());
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) if e1 == e2 => {
                sub.bty_subtyping(bty1, bty2);
                return;
            }
            (TyKind::Exists(bty1, p1), TyKind::Exists(bty2, p2)) if p1 == p2 => {
                sub.bty_subtyping(bty1, bty2);
                return;
            }
            (TyKind::Exists(bty, p), _) => {
                let fresh = sub
                    .cursor
                    .push_binding(bty.sort(), |fresh| p.subst_bound_vars(Var::Free(fresh)));
                let ty1 = TyKind::Refine(bty.clone(), Var::Free(fresh).into()).intern();
                sub.subtyping(ty1, ty2);
                return;
            }
            _ => {}
        }

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                sub.bty_subtyping(bty1, bty2);
                sub.cursor
                    .push_head(ExprKind::BinaryOp(BinOp::Eq, e1.clone(), e2.clone()).intern());
            }
            (TyKind::Refine(bty1, e), TyKind::Exists(bty2, p)) => {
                sub.bty_subtyping(bty1, bty2);
                let p = p.subst_bound_vars(e.clone());
                sub.cursor.push_head(p.subst_bound_vars(e.clone()))
            }
            (TyKind::StrgRef(loc1), TyKind::StrgRef(loc2)) => {
                assert_eq!(loc1, loc2);
            }
            (TyKind::Ref(ty1), TyKind::Ref(ty2)) => {
                sub.subtyping(ty1.clone(), ty2.clone());
                sub.subtyping(ty2.clone(), ty1.clone());
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
            }
            (TyKind::Param(param1), TyKind::Param(param2)) => {
                debug_assert_eq!(param1, param2)
            }
            (TyKind::Exists(..), _) => {
                unreachable!("subtyping with unpacked existential")
            }
            _ => {
                unreachable!("unexpected types: `{:?}` `{:?}`", ty1, ty2)
            }
        }
    }

    fn bty_subtyping(&mut self, bty1: &BaseTy, bty2: &BaseTy) {
        match (bty1, bty2) {
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
            }
            (BaseTy::Bool, BaseTy::Bool) => {}
            (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) => {
                debug_assert_eq!(did1, did2);
                debug_assert_eq!(substs1.len(), substs2.len());
                let variances = self.tcx.variances_of(*did1);
                for (variance, ty1, ty2) in izip!(variances, substs1.iter(), substs2.iter()) {
                    self.polymorphic_subtyping(*variance, ty1.clone(), ty2.clone());
                }
            }
            _ => unreachable!("unexpected base types: `{:?}` `{:?}`", bty1, bty2),
        }
    }

    fn polymorphic_subtyping(&mut self, variance: rustc_middle::ty::Variance, ty1: Ty, ty2: Ty) {
        match variance {
            rustc_middle::ty::Variance::Covariant => {
                self.subtyping(ty1, ty2);
            }
            rustc_middle::ty::Variance::Invariant => {
                self.subtyping(ty1.clone(), ty2.clone());
                self.subtyping(ty2, ty1);
            }
            rustc_middle::ty::Variance::Contravariant => {
                self.subtyping(ty2, ty1);
            }
            rustc_middle::ty::Variance::Bivariant => {}
        }
    }
}
