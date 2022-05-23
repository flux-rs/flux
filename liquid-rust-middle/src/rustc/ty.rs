//! A simplified version of rust types.

use rustc_hir::def_id::DefId;
pub use rustc_middle::{
    mir::Mutability,
    ty::{FloatTy, IntTy, ParamTy, UintTy},
};

use crate::intern::{impl_internable, Interned, List};

#[derive(Debug)]
pub struct FnSig {
    inputs_and_output: List<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ty(Interned<TyS>);

#[derive(Debug, PartialEq, Eq, Hash)]
struct TyS {
    kind: TyKind,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    Adt(DefId, List<GenericArg>),
    Bool,
    Float(FloatTy),
    Int(IntTy),
    Never,
    Param(ParamTy),
    Ref(Ty, Mutability),
    Tuple(List<Ty>),
    Uint(UintTy),
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
}

impl FnSig {
    pub fn inputs(&self) -> &[Ty] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> Ty {
        self.inputs_and_output[self.inputs_and_output.len() - 1].clone()
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Ty(Interned::new(TyS { kind: self }))
    }
}

impl Ty {
    pub fn mk_adt(def_id: DefId, substs: impl Into<List<GenericArg>>) -> Ty {
        TyKind::Adt(def_id, substs.into()).intern()
    }

    pub fn mk_bool() -> Ty {
        TyKind::Bool.intern()
    }

    pub fn mk_float(float_ty: FloatTy) -> Ty {
        TyKind::Float(float_ty).intern()
    }

    pub fn mk_int(int_ty: IntTy) -> Ty {
        TyKind::Int(int_ty).intern()
    }

    pub fn mk_never() -> Ty {
        TyKind::Never.intern()
    }

    pub fn mk_param(param: ParamTy) -> Ty {
        TyKind::Param(param).intern()
    }

    pub fn mk_ref(ty: Ty, mutability: Mutability) -> Ty {
        TyKind::Ref(ty, mutability).intern()
    }

    pub fn mk_tuple(tys: impl Into<List<Ty>>) -> Ty {
        TyKind::Tuple(tys.into()).intern()
    }

    pub fn mk_uint(uint_ty: UintTy) -> Ty {
        TyKind::Uint(uint_ty).intern()
    }

    pub fn kind(&self) -> &TyKind {
        &self.0.kind
    }
}

impl_internable!(TyS, [Ty], [GenericArg]);
