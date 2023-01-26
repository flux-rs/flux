///! "Lift" HIR types into  FHIR types.
use flux_common::{bug, iter::IterExt};
use flux_errors::ErrorGuaranteed;
use hir::{def::DefKind, def_id::DefId};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_span::DUMMY_SP;

use crate::{early_ctxt::EarlyCtxt, fhir};

pub fn lift_adt_def(early_cx: &EarlyCtxt, def_id: LocalDefId) -> fhir::AdtDef {
    let item = early_cx.tcx.hir().expect_item(def_id);
    match item.kind {
        hir::ItemKind::TyAlias(ty, _) => {
            let refined_by = fhir::RefinedBy { params: vec![], early_bound: 0, span: ty.span };
            fhir::AdtDef::new(def_id, refined_by)
        }
        hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => {
            todo!("implement lifting for structs and enums")
        }
        _ => {
            bug!("expected type alias");
        }
    }
}

pub fn lift_alias(
    early_cx: &EarlyCtxt,
    def_id: LocalDefId,
) -> Result<fhir::Alias, ErrorGuaranteed> {
    let item = early_cx.tcx.hir().expect_item(def_id);
    let hir::ItemKind::TyAlias(ty, _) = &item.kind else {
        bug!("expected type alias");
    };
    let refined_by = fhir::RefinedBy { params: vec![], early_bound: 0, span: DUMMY_SP };
    let ty = lift_ty(early_cx, ty)?;
    Ok(fhir::Alias { def_id, refined_by, ty, span: item.span })
}

pub fn lift_fn_sig(
    early_cx: &EarlyCtxt,
    def_id: LocalDefId,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    let hir_id = early_cx.hir().local_def_id_to_hir_id(def_id);
    let fn_decl = early_cx
        .hir()
        .fn_decl_by_hir_id(hir_id)
        .expect("item is does not have a `FnDecl`");

    let args = fn_decl
        .inputs
        .iter()
        .map(|ty| lift_ty(early_cx, ty))
        .try_collect_exhaust()?;

    let output = fhir::FnOutput {
        params: vec![],
        ensures: vec![],
        ret: lift_fn_ret_ty(early_cx, &fn_decl.output)?,
    };

    Ok(fhir::FnSig { params: vec![], requires: vec![], args, output })
}

fn lift_fn_ret_ty(
    early_cx: &EarlyCtxt,
    ret_ty: &hir::FnRetTy,
) -> Result<fhir::Ty, ErrorGuaranteed> {
    match ret_ty {
        hir::FnRetTy::DefaultReturn(_) => Ok(fhir::Ty::Tuple(vec![])),
        hir::FnRetTy::Return(ty) => lift_ty(early_cx, ty),
    }
}

fn lift_ty(early_cx: &EarlyCtxt, ty: &hir::Ty) -> Result<fhir::Ty, ErrorGuaranteed> {
    let ty = match &ty.kind {
        hir::TyKind::Slice(ty) => fhir::BaseTy::Slice(Box::new(lift_ty(early_cx, ty)?)).into(),
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
        hir::TyKind::Path(hir::QPath::Resolved(_, path)) => lift_path(early_cx, path)?,
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

fn lift_path(early_cx: &EarlyCtxt, path: &hir::Path) -> Result<fhir::Ty, ErrorGuaranteed> {
    let ty = match path.res {
        hir::def::Res::Def(DefKind::Struct | DefKind::Enum, def_id) => {
            let args = path.segments.last().unwrap().args;
            fhir::Ty::BaseTy(fhir::BaseTy::Adt(def_id, lift_generic_args(early_cx, args)?))
        }
        hir::def::Res::Def(DefKind::TyAlias, def_id) => {
            let args = path.segments.last().unwrap().args;
            fhir::BaseTy::Alias(def_id, lift_generic_args(early_cx, args)?, vec![]).into()
        }
        hir::def::Res::Def(DefKind::TyParam, def_id) => fhir::Ty::Param(def_id),
        hir::def::Res::PrimTy(hir::PrimTy::Bool) => fhir::BaseTy::Bool.into(),
        hir::def::Res::PrimTy(hir::PrimTy::Char) => fhir::Ty::Char,
        hir::def::Res::PrimTy(hir::PrimTy::Str) => fhir::Ty::Str,
        hir::def::Res::PrimTy(hir::PrimTy::Int(int_ty)) => fhir::BaseTy::Int(int_ty).into(),
        hir::def::Res::PrimTy(hir::PrimTy::Uint(uint_ty)) => fhir::BaseTy::Uint(uint_ty).into(),
        hir::def::Res::PrimTy(hir::PrimTy::Float(float_ty)) => fhir::Ty::Float(float_ty),
        hir::def::Res::SelfTyAlias { alias_to, .. } => lift_self_ty_alias(early_cx, alias_to)?,
        hir::def::Res::Def(kind, def_id) => todo!("{kind:?} {def_id:?}"),
        hir::def::Res::SelfTyParam { .. } => todo!(),
        hir::def::Res::SelfCtor(_) => todo!(),
        hir::def::Res::Local(_) => todo!(),
        hir::def::Res::ToolMod => todo!(),
        hir::def::Res::NonMacroAttr(_) => todo!(),
        hir::def::Res::Err => todo!(),
    };
    Ok(ty)
}

fn lift_self_ty_alias(early_cx: &EarlyCtxt, alias_to: DefId) -> Result<fhir::Ty, ErrorGuaranteed> {
    let hir = early_cx.hir();
    let def_id = alias_to.expect_local();
    match hir.expect_item(def_id).kind {
        hir::ItemKind::Impl(parent_impl) => lift_ty(early_cx, parent_impl.self_ty),
        _ => todo!(),
    }
}

fn lift_generic_args(
    early_cx: &EarlyCtxt,
    args: Option<&hir::GenericArgs>,
) -> Result<Vec<fhir::Ty>, ErrorGuaranteed> {
    let mut filtered = vec![];
    if let Some(args) = args {
        for arg in args.args {
            match arg {
                hir::GenericArg::Lifetime(_) => {}
                hir::GenericArg::Type(ty) => filtered.push(lift_ty(early_cx, ty)?),
                hir::GenericArg::Const(_) => todo!("const generic are not supported"),
                hir::GenericArg::Infer(_) => {
                    bug!("unexpected inference generic argument");
                }
            }
        }
    }
    Ok(filtered)
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
