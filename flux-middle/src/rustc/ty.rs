//! A simplified version of rust types.

use itertools::Itertools;
use rustc_hir::def_id::DefId;
pub use rustc_middle::{
    mir::Mutability,
    ty::{FloatTy, IntTy, ParamTy, ScalarInt, UintTy},
};

use crate::intern::{impl_internable, Interned, List};

pub struct Generics<'tcx> {
    pub params: List<GenericParamDef>,
    pub rustc: &'tcx rustc_middle::ty::Generics,
}

#[derive(Hash, Eq, PartialEq)]
pub struct GenericParamDef {
    pub def_id: DefId,
    pub kind: GenericParamDefKind,
}

#[derive(Hash, Eq, PartialEq)]
pub enum GenericParamDefKind {
    Type { has_default: bool },
}

#[derive(Debug)]
pub struct FnSig {
    pub(crate) inputs_and_output: List<Ty>,
}

#[derive(Debug)]
pub struct EnumDef {
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct VariantDef {
    pub fields: List<Ty>,
    pub ret: Ty,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Ty(Interned<TyS>);

#[derive(Debug, PartialEq, Eq, Hash)]
struct TyS {
    kind: TyKind,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    Adt(DefId, List<GenericArg>),
    Array(Ty, Const),
    Bool,
    Str,
    Float(FloatTy),
    Int(IntTy),
    Never,
    Param(ParamTy),
    Ref(Ty, Mutability),
    Tuple(List<Ty>),
    Uint(UintTy),
}

#[derive(PartialEq, Eq, Hash)]
pub struct Const {
    pub ty: Ty,
    pub kind: ConstKind,
}

#[derive(PartialEq, Eq, Hash)]
pub enum ConstKind {
    Value(ValTree),
}

#[derive(PartialEq, Eq, Hash)]
pub enum ValTree {
    Leaf(ScalarInt),
}

#[derive(PartialEq, Eq, Hash)]
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

    pub fn mk_array(ty: Ty, c: Const) -> Ty {
        TyKind::Array(ty, c).intern()
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

    pub fn mk_str() -> Ty {
        TyKind::Str.intern()
    }

    pub fn kind(&self) -> &TyKind {
        &self.0.kind
    }
}

impl_internable!(TyS, [Ty], [GenericArg], [GenericParamDef]);

impl std::fmt::Debug for GenericArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GenericArg::Ty(ty) => write!(f, "{ty:?}"),
        }
    }
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            TyKind::Adt(def_id, substs) => {
                let adt_name = rustc_middle::ty::tls::with(|tcx| {
                    let path = tcx.def_path(*def_id);
                    path.data.iter().join("::")
                });
                write!(f, "{adt_name}")?;
                if !substs.is_empty() {
                    write!(
                        f,
                        "<{}>",
                        substs
                            .iter()
                            .format_with(", ", |arg, f| f(&format_args!("{:?}", arg)))
                    )?;
                }
                Ok(())
            }
            TyKind::Bool => write!(f, "bool"),
            TyKind::Str => write!(f, "str"),
            TyKind::Float(float_ty) => write!(f, "{}", float_ty.name_str()),
            TyKind::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
            TyKind::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
            TyKind::Never => write!(f, "!"),
            TyKind::Param(param_ty) => write!(f, "{param_ty}"),
            TyKind::Ref(ty, Mutability::Mut) => write!(f, "&mut {ty:?}"),
            TyKind::Ref(ty, Mutability::Not) => write!(f, "&{ty:?}"),
            TyKind::Array(ty, c) => write!(f, "[{ty:?}; {c:?}]"),
            TyKind::Tuple(tys) => {
                write!(
                    f,
                    "({})",
                    tys.iter()
                        .format_with(", ", |ty, f| f(&format_args!("{:?}", ty)))
                )
            }
        }
    }
}

impl std::fmt::Debug for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ConstKind::Value(val) => write!(f, "{val:?}"),
        }
    }
}

impl std::fmt::Debug for ValTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValTree::Leaf(scalar) => write!(f, "{scalar:?}"),
        }
    }
}
