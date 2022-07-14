//! A simplified version of rust types.

use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
pub use rustc_middle::{
    mir::Mutability,
    ty::{FloatTy, IntTy, ParamTy, UintTy},
};

use crate::intern::{impl_internable, Interned, List};

#[derive(Debug)]
pub struct FnSig {
    pub(crate) inputs_and_output: List<Ty>,
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
    Bool,
    Float(FloatTy),
    Int(IntTy),
    Never,
    Param(ParamTy),
    Ref(Ty, Mutability),
    Tuple(List<Ty>),
    Uint(UintTy),
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum GenericArg {
    Ty(Ty),
    // LifetimeOrConst,
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

impl std::fmt::Debug for GenericArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GenericArg::Ty(ty) => write!(f, "{ty:?}"),
            // GenericArg::LifetimeOrConst => write!(f, "_|_"),
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
            TyKind::Float(float_ty) => write!(f, "{}", float_ty.name_str()),
            TyKind::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
            TyKind::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
            TyKind::Never => write!(f, "!"),
            TyKind::Param(param_ty) => write!(f, "{param_ty}"),
            TyKind::Ref(ty, Mutability::Mut) => write!(f, "&mut {ty:?}"),
            TyKind::Ref(ty, Mutability::Not) => write!(f, "&{ty:?}"),
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

/// We want to build a lookup table: `(trait_f, key) -> trait_f_ty_at_key` that maps
/// (1) `trait_f` the generic method name `DefId` which appears at usage-sites,
/// (2) `key` the particular type-args at the usage site
/// to the `trait_f_ty_at_key` which is the specific method instance at the key
///
/// e.g. Given (std::Iterator.next, Rng) -> Rng.next
/// Table is creating a map
///
///     method_def_id, subst -> impl_def_id
///
pub type TraitRefKey = DefId;
pub type TraitImplMap = FxHashMap<(DefId, TraitRefKey), DefId>;

pub fn rustc_substs_trait_ref_key(
    substs: &rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg>,
) -> Option<TraitRefKey> {
    match substs.get(0)?.unpack() {
        rustc_middle::ty::subst::GenericArgKind::Type(ty) => {
            match ty.kind() {
                rustc_middle::ty::TyKind::Adt(def, _) => Some(def.did()),
                _ => None,
            }
        }
        _ => None,
    }
}

// TODO:RJ gross to have to duplicate ...
pub fn flux_substs_trait_ref_key(substs: &List<GenericArg>) -> Option<TraitRefKey> {
    match substs.get(0)? {
        GenericArg::Ty(ty) => {
            match ty.kind() {
                TyKind::Adt(def_id, _) => Some(*def_id),
                _ => None,
            }
        }
    }
}
