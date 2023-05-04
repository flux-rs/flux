//! A simplified version of rust types.

use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::ty::ClosureKind;
pub use rustc_middle::{
    mir::Mutability,
    ty::{
        BoundVar, DebruijnIndex, EarlyBinder, EarlyBoundRegion, FloatTy, IntTy, ParamTy, RegionVid,
        ScalarInt, UintTy,
    },
};
use rustc_span::Symbol;

use crate::intern::{impl_internable, Interned, List};

pub struct Generics<'tcx> {
    pub params: List<GenericParamDef>,
    pub orig: &'tcx rustc_middle::ty::Generics,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Binder<T>(T, List<BoundVariableKind>);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Encodable, Decodable)]
pub enum BoundVariableKind {
    Region(BoundRegionKind),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Encodable, Decodable)]
pub enum BoundRegionKind {
    BrAnon,
    BrNamed(DefId, Symbol),
}

#[derive(Hash, Eq, PartialEq)]
pub struct GenericParamDef {
    pub def_id: DefId,
    pub index: u32,
    pub name: Symbol,
    pub kind: GenericParamDefKind,
}

#[derive(Hash, Eq, PartialEq)]
pub enum GenericParamDefKind {
    Type { has_default: bool },
    Lifetime,
}

#[derive(Debug)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    pub predicates: List<Predicate>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Predicate {
    pub kind: Binder<PredicateKind>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum PredicateKind {
    FnTrait { bounded_ty: Ty, tupled_args: Ty, output: Ty, kind: ClosureKind },
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct FnSig {
    pub(crate) inputs_and_output: List<Ty>,
}

pub type PolyFnSig = Binder<FnSig>;

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
    Char,
    Float(FloatTy),
    Int(IntTy),
    Never,
    Param(ParamTy),
    Ref(Region, Ty, Mutability),
    Tuple(List<Ty>),
    Uint(UintTy),
    Slice(Ty),
    FnSig(PolyFnSig),
    Closure(DefId, List<GenericArg>),
    RawPtr(Ty, Mutability),
}

#[derive(Clone, PartialEq, Eq, Hash, Encodable, Decodable)]
pub struct Const {
    pub val: usize,
}

#[derive(PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Region),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Region {
    ReLateBound(DebruijnIndex, BoundRegion),
    ReEarlyBound(EarlyBoundRegion),
    ReStatic,
    ReVar(RegionVid),
    ReErased,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Encodable, Decodable)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

impl Predicate {
    pub(crate) fn new(kind: Binder<PredicateKind>) -> Predicate {
        Predicate { kind }
    }
}

impl<T> Binder<T> {
    pub fn bind_with_vars(value: T, vars: impl Into<List<BoundVariableKind>>) -> Binder<T> {
        Binder(value, vars.into())
    }

    pub fn skip_binder(self) -> T {
        self.0
    }

    pub fn as_ref(&self) -> Binder<&T> {
        Binder(&self.0, self.1.clone())
    }

    pub fn vars(&self) -> &List<BoundVariableKind> {
        &self.1
    }
}

impl FnSig {
    pub fn inputs(&self) -> &[Ty] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Ty {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
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

    pub fn mk_closure(def_id: DefId, substs: impl Into<List<GenericArg>>) -> Ty {
        TyKind::Closure(def_id, substs.into()).intern()
    }

    pub fn mk_array(ty: Ty, c: Const) -> Ty {
        TyKind::Array(ty, c).intern()
    }

    pub fn mk_slice(ty: Ty) -> Ty {
        TyKind::Slice(ty).intern()
    }

    pub fn mk_fn_sig(fn_sig: PolyFnSig) -> Ty {
        TyKind::FnSig(fn_sig).intern()
    }

    pub fn mk_raw_ptr(ty: Ty, mutbl: Mutability) -> Ty {
        TyKind::RawPtr(ty, mutbl).intern()
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

    pub fn mk_ref(region: Region, ty: Ty, mutability: Mutability) -> Ty {
        TyKind::Ref(region, ty, mutability).intern()
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

    pub fn mk_char() -> Ty {
        TyKind::Char.intern()
    }

    pub fn mk_usize() -> Ty {
        TyKind::Uint(UintTy::Usize).intern()
    }

    pub fn kind(&self) -> &TyKind {
        &self.0.kind
    }
}

impl_internable!(TyS, [Ty], [GenericArg], [GenericParamDef], [BoundVariableKind], [Predicate]);

impl std::fmt::Debug for GenericArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GenericArg::Ty(ty) => write!(f, "{ty:?}"),
            GenericArg::Lifetime(region) => write!(f, "{region:?}"),
        }
    }
}

impl std::fmt::Debug for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Region::ReLateBound(_, bregion) => write!(f, "{bregion:?}"),
            Region::ReEarlyBound(bregion) => write!(f, "{bregion:?}"),
            Region::ReStatic => write!(f, "'static"),
            Region::ReVar(rvid) => write!(f, "{rvid:?}"),
            Region::ReErased => write!(f, "ReErased"),
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
                    write!(f, "<{:?}>", substs.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::Bool => write!(f, "bool"),
            TyKind::Str => write!(f, "str"),
            TyKind::Char => write!(f, "char"),
            TyKind::Float(float_ty) => write!(f, "{}", float_ty.name_str()),
            TyKind::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
            TyKind::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
            TyKind::Never => write!(f, "!"),
            TyKind::Param(param_ty) => write!(f, "{param_ty}"),
            TyKind::Ref(region, ty, Mutability::Mut) => write!(f, "&{region:?} mut {ty:?}"),
            TyKind::Ref(region, ty, Mutability::Not) => write!(f, "&{region:?} {ty:?}"),
            TyKind::Array(ty, c) => write!(f, "[{ty:?}; {c:?}]"),
            TyKind::Tuple(tys) => {
                if let [ty] = &tys[..] {
                    write!(f, "({ty:?},)")
                } else {
                    write!(f, "({:?})", tys.iter().format(", "))
                }
            }
            TyKind::Slice(ty) => write!(f, "[{ty:?}]"),
            TyKind::RawPtr(ty, Mutability::Mut) => write!(f, "*mut {ty:?}"),
            TyKind::RawPtr(ty, Mutability::Not) => write!(f, "*const {ty:?}"),
            TyKind::FnSig(fn_sig) => write!(f, "{fn_sig:?}"),
            TyKind::Closure(did, substs) => {
                write!(f, "Closure {did:?}")?;
                if !substs.is_empty() {
                    write!(f, "<{:?}>", substs.iter().format(", "))?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Debug for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_")
    }
}
