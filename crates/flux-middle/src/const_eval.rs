use rustc_middle::ty::{self as rustc_ty, ParamEnv, TyCtxt, TyKind};
use rustc_type_ir::{IntTy, UintTy};

use crate::rustc::{self, lowering::lower_ty, mir::Constant};

// FIXME(nilehmann) We are using this during lowering to evaluate constants annotated. We should
// do the evaluation later in the pipeline.
pub fn scalar_int_to_rty_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<crate::rty::Constant> {
    use rustc_middle::ty::TyKind;
    match ty.kind() {
        TyKind::Int(int_ty) => {
            Some(crate::rty::Constant::from(scalar_to_int(tcx, scalar, *int_ty)))
        }
        TyKind::Uint(uint_ty) => {
            Some(crate::rty::Constant::from(scalar_to_uint(tcx, scalar, *uint_ty)))
        }
        TyKind::Bool => {
            let b = scalar_to_bits(tcx, scalar, ty)?;
            Some(crate::rty::Constant::Bool(b != 0))
        }
        _ => None,
    }
}

pub fn scalar_int_to_rty_constant2(
    tcx: TyCtxt,
    scalar: rustc_ty::ScalarInt,
    ty: &rustc::ty::Ty,
) -> Option<crate::rty::Constant> {
    use rustc::ty::TyKind;
    match ty.kind() {
        TyKind::Int(int_ty) => {
            Some(crate::rty::Constant::from(scalar_to_int(tcx, scalar, *int_ty)))
        }
        TyKind::Uint(uint_ty) => {
            Some(crate::rty::Constant::from(scalar_to_uint(tcx, scalar, *uint_ty)))
        }
        TyKind::Bool => Some(crate::rty::Constant::Bool(scalar.try_to_bool().unwrap())),
        _ => None,
    }
}

pub fn scalar_int_to_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Constant> {
    let kind = ty.kind();
    match kind {
        TyKind::Int(int_ty) => Some(Constant::Int(scalar_to_int(tcx, scalar, *int_ty), *int_ty)),
        TyKind::Uint(uint_ty) => {
            Some(Constant::Uint(scalar_to_uint(tcx, scalar, *uint_ty), *uint_ty))
        }
        TyKind::Float(float_ty) => {
            Some(Constant::Float(scalar_to_bits(tcx, scalar, ty).unwrap(), *float_ty))
        }
        TyKind::Char => Some(Constant::Char),
        TyKind::Bool => Some(Constant::Bool(scalar.try_to_bool().unwrap())),
        TyKind::Tuple(tys) if tys.is_empty() => Some(Constant::Unit),
        _ => {
            match lower_ty(tcx, ty) {
                Ok(ty) => Some(Constant::Opaque(ty)),
                Err(_) => None,
            }
        }
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
    scalar.try_to_bits(size).ok()
}

fn scalar_to_int(tcx: TyCtxt, scalar: rustc_ty::ScalarInt, int_ty: IntTy) -> i128 {
    scalar.to_int(size_of_int_ty(tcx, int_ty))
}

fn scalar_to_uint(tcx: TyCtxt<'_>, scalar: rustc_ty::ScalarInt, uint_ty: UintTy) -> u128 {
    scalar.to_uint(size_of_uint_ty(tcx, uint_ty))
}

fn size_of_int_ty(tcx: TyCtxt, int_ty: IntTy) -> rustc_abi::Size {
    match int_ty {
        IntTy::I8 => rustc_abi::Size::from_bits(8),
        IntTy::I16 => rustc_abi::Size::from_bits(16),
        IntTy::I32 => rustc_abi::Size::from_bits(32),
        IntTy::I64 => rustc_abi::Size::from_bits(64),
        IntTy::I128 => rustc_abi::Size::from_bits(128),
        IntTy::Isize => tcx.data_layout.pointer_size,
    }
}

fn size_of_uint_ty(tcx: TyCtxt, uint_ty: UintTy) -> rustc_abi::Size {
    match uint_ty {
        UintTy::U8 => rustc_abi::Size::from_bits(8),
        UintTy::U16 => rustc_abi::Size::from_bits(16),
        UintTy::U32 => rustc_abi::Size::from_bits(32),
        UintTy::U64 => rustc_abi::Size::from_bits(64),
        UintTy::U128 => rustc_abi::Size::from_bits(128),
        UintTy::Usize => tcx.data_layout.pointer_size,
    }
}
