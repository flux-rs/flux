use flux_common::bug;
use flux_errors::ErrorGuaranteed;
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;

use crate::{early_ctxt::EarlyCtxt, fhir};

fn lift_alias(early_cx: &EarlyCtxt, def_id: LocalDefId) -> fhir::Alias {
    let hir::ItemKind::TyAlias(hir_ty, _) = &early_cx.tcx.hir().expect_item(def_id).kind else {
        bug!("expected type alias");
    };
    todo!()
}

fn lift_ty(early_cx: &EarlyCtxt, ty: &hir::Ty) -> Result<fhir::Ty, ErrorGuaranteed> {
    let ty = match &ty.kind {
        hir::TyKind::Slice(ty) => {
            fhir::Ty::BaseTy(fhir::BaseTy::Slice(Box::new(lift_ty(early_cx, ty)?)))
        }
        hir::TyKind::Array(ty, len) => {
            fhir::Ty::Array(Box::new(lift_ty(early_cx, ty)?), lift_array_len(early_cx, len)?)
        }
        hir::TyKind::Ref(_, mut_ty) => {
            fhir::Ty::Ref(lift_mutability(mut_ty.mutbl), Box::new(lift_ty(early_cx, mut_ty.ty)?))
        }
        hir::TyKind::Never => fhir::Ty::Never,
        hir::TyKind::Tup(tys) => {
            fhir::Ty::Tuple(tys.iter().map(|ty| lift_ty(early_cx, ty)).try_collect()?)
        }
        hir::TyKind::Path(hir::QPath::Resolved(_, path)) => todo!(),
        hir::TyKind::Path(_)
        | hir::TyKind::OpaqueDef(_, _, _)
        | hir::TyKind::TraitObject(_, _, _)
        | hir::TyKind::Typeof(_)
        | hir::TyKind::BareFn(_)
        | hir::TyKind::Ptr(_)
        | hir::TyKind::Infer
        | hir::TyKind::Err => todo!(),
    };
    Ok(ty)
}

fn lift_mutability(mtbl: hir::Mutability) -> fhir::RefKind {
    match mtbl {
        hir::Mutability::Mut => fhir::RefKind::Mut,
        hir::Mutability::Not => fhir::RefKind::Shr,
    }
}

fn lift_array_len(
    early_cx: &EarlyCtxt,
    len: &hir::ArrayLen,
) -> Result<fhir::ArrayLen, ErrorGuaranteed> {
    let body = match len {
        hir::ArrayLen::Body(anon_const) => early_cx.hir().body(anon_const.body),
        hir::ArrayLen::Infer(_, _) => bug!("unexpected `ArrayLen::Infer`"),
    };
    if let hir::ExprKind::Lit(lit) = &body.value.kind
            && let LitKind::Int(array_len, _) = lit.node
    {
        Ok(fhir::ArrayLen {val: array_len as usize })
    } else {
        todo!()
    }
}
