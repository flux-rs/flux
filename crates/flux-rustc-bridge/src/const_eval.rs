use rustc_middle::ty::{self as rustc_ty, ParamEnv, TyCtxt};
use rustc_type_ir::{IntTy, UintTy};

pub enum SimpleConst {
    Int(i128),
    Uint(u128),
    Bool(bool),
}

pub fn scalar_int_to_simpl_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<SimpleConst> {
    use rustc_middle::ty::TyKind;
    match ty.kind() {
        TyKind::Int(int_ty) => Some(SimpleConst::Int(scalar_to_int(tcx, scalar, *int_ty))),
        TyKind::Uint(uint_ty) => Some(SimpleConst::Uint(scalar_to_uint(tcx, scalar, *uint_ty))),
        TyKind::Bool => {
            let b = scalar_to_bits(tcx, scalar, ty)?;
            Some(SimpleConst::Bool(b != 0))
        }
        _ => None,
    }
}

pub fn scalar_to_bits<'tcx>(
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

pub fn scalar_to_int(tcx: TyCtxt, scalar: rustc_ty::ScalarInt, int_ty: IntTy) -> i128 {
    scalar.to_int(size_of_int_ty(tcx, int_ty))
}

pub fn scalar_to_uint(tcx: TyCtxt<'_>, scalar: rustc_ty::ScalarInt, uint_ty: UintTy) -> u128 {
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
