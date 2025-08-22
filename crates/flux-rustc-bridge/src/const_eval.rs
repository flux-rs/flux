use rustc_middle::ty::{self as rustc_ty, ParamEnv, TyCtxt, TypingEnv, TypingMode};
use rustc_type_ir::{IntTy, UintTy};

pub fn scalar_to_bits<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let typing_env =
        TypingEnv { param_env: ParamEnv::empty(), typing_mode: TypingMode::non_body_analysis() };
    let size = tcx.layout_of(typing_env.as_query_input(ty)).unwrap().size;
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
        IntTy::Isize => tcx.data_layout.pointer_size(),
    }
}

fn size_of_uint_ty(tcx: TyCtxt, uint_ty: UintTy) -> rustc_abi::Size {
    match uint_ty {
        UintTy::U8 => rustc_abi::Size::from_bits(8),
        UintTy::U16 => rustc_abi::Size::from_bits(16),
        UintTy::U32 => rustc_abi::Size::from_bits(32),
        UintTy::U64 => rustc_abi::Size::from_bits(64),
        UintTy::U128 => rustc_abi::Size::from_bits(128),
        UintTy::Usize => tcx.data_layout.pointer_size(),
    }
}
