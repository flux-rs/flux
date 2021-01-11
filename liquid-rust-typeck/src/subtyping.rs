use liquid_rust_core::ty::{self, pred, subst::Subst, Ty, TyCtxt, TyS};
use pred::Place;
use ty::{Heap, LocalsMap, TyKind};

use crate::constraint::Constraint;

pub fn subtyping(tcx: &TyCtxt, heap1: &Heap, ty1: &TyS, heap2: &Heap, ty2: &TyS) -> Constraint {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Fn(..), TyKind::Fn(..)) => todo!(),
        (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => tup1
            .iter()
            .zip(tup2.types())
            .rev()
            .fold(Constraint::True, |c, ((x, ty1), ty2)| {
                Constraint::Conj(vec![
                    subtyping(tcx, heap1, ty1, heap2, ty2),
                    Constraint::from_binding(*x, ty1.clone(), c),
                ])
            }),
        // TODO check regions
        (TyKind::Ref(bk1, _, l1), TyKind::Ref(bk2, _, l2)) if bk1 >= bk2 => {
            let ty1 = &tcx.selfify(&heap1[l1], Place::from(*l1));
            let ty2 = &heap2[l2];
            subtyping(tcx, heap1, ty1, heap2, ty2)
        }
        (TyKind::OwnRef(l1), TyKind::OwnRef(l2)) => {
            let ty1 = &tcx.selfify(&heap1[l1], Place::from(*l1));
            let ty2 = &heap2[l2];
            subtyping(tcx, heap1, ty1, heap2, ty2)
        }
        (TyKind::Refine(bty1, refine1), TyKind::Refine(bty2, refine2)) if bty1 == bty2 => {
            Constraint::from_subtype(bty1, refine1, refine2)
        }
        (_, TyKind::Uninit(n)) if ty1.size() == *n => Constraint::True,
        _ => bug!("{} {}", ty1, ty2),
    }
}

pub fn infer_subst(heap1: &Heap, locals1: &LocalsMap, heap2: &Heap, locals2: &LocalsMap) -> Subst {
    let mut subst = Subst::new();
    for (x, l2) in locals2 {
        let l1 = &locals1[x];
        let ty1 = &heap1[l1];
        let ty2 = &heap2[l2];
        subst.add_location_subst(*l2, *l1);
        infer_subst_ty(&mut subst, heap1, ty1, heap2, ty2);
    }
    subst
}

fn infer_subst_ty(subst: &mut Subst, heap1: &Heap, ty1: &Ty, heap2: &Heap, ty2: &Ty) {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Ref(.., l1), TyKind::Ref(.., l2)) | (TyKind::OwnRef(l1), TyKind::OwnRef(l2)) => {
            subst.add_location_subst(*l1, *l2);
            infer_subst_ty(subst, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
            for ((fld1, ty1), (fld2, ty2)) in tup1.iter().zip(tup2) {
                subst.add_field_subst(*fld1, *fld2);
                infer_subst_ty(subst, heap1, ty1, heap2, ty2);
            }
        }
        _ => {}
    }
}
