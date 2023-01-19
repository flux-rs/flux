use flux_fixpoint::Sign::{Negative, Positive};
use rustc_middle::ty::{self as rustc_ty, ParamEnv, TyCtxt, TyKind};

use crate::rustc::mir::Constant;
pub fn scalar_int_to_rty_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<crate::rty::Constant> {
    match ty.kind() {
        TyKind::Int(_) => {
            let i = scalar_to_int(tcx, scalar, ty)?;
            crate::rty::Constant::from(i)
        }
        TyKind::Uint(_) => {
            let u = scalar_to_uint(tcx, scalar, ty)?;
            Some(crate::rty::Constant::Int(Positive, u))
        }
        TyKind::Bool => {
            let b = scalar_to_bits(tcx, scalar, ty)?;
            Some(crate::rty::Constant::Bool(b != 0))
        }
        _ => None,
    }
}

pub fn scalar_int_to_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Constant> {
    match ty.kind() {
        TyKind::Int(int_ty) => {
            Some(Constant::Int(scalar_to_int(tcx, scalar, ty).unwrap(), *int_ty))
        }
        TyKind::Uint(int_ty) => {
            Some(Constant::Uint(scalar_to_uint(tcx, scalar, ty).unwrap(), *int_ty))
        }
        TyKind::Float(float_ty) => {
            Some(Constant::Float(scalar_to_bits(tcx, scalar, ty).unwrap(), *float_ty))
        }
        TyKind::Char => Some(Constant::Char),
        TyKind::Bool => Some(Constant::Bool(scalar_to_bits(tcx, scalar, ty).unwrap() != 0)),
        TyKind::Tuple(tys) if tys.is_empty() => Some(Constant::Unit),
        _ => None,
    }
}

fn scalar_to_bits<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.to_bits(size).ok()
}

fn scalar_to_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_ty::Ty<'tcx>,
) -> Option<i128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.try_to_int(size).ok()
}

fn scalar_to_uint<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.try_to_uint(size).ok()
}
