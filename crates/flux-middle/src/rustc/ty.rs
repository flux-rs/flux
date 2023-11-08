//! A simplified version of rust types.

mod subst;

use std::fmt;

use flux_common::bug;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_index::{IndexSlice, IndexVec};
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::ty::{AdtFlags, ParamConst};
pub use rustc_middle::{
    mir::Mutability,
    ty::{
        BoundRegionKind, BoundVar, DebruijnIndex, EarlyBoundRegion, FloatTy, IntTy, ParamTy,
        RegionVid, ScalarInt, UintTy,
    },
};
use rustc_span::{symbol::kw, Symbol};
use rustc_target::abi::{FieldIdx, VariantIdx, FIRST_VARIANT};

use self::subst::Subst;
use crate::{
    intern::{impl_internable, impl_slice_internable, Interned, List},
    pretty::def_id_to_string,
};

pub struct Generics<'tcx> {
    pub params: List<GenericParamDef>,
    pub orig: &'tcx rustc_middle::ty::Generics,
}

#[derive(Clone)]
pub struct EarlyBinder<T>(pub T);

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Binder<T>(T, List<BoundVariableKind>);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub enum BoundVariableKind {
    Region(BoundRegionKind),
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
    Const { has_default: bool },
}

#[derive(Debug)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    pub predicates: List<Clause>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Clause {
    pub kind: ClauseKind,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    Projection(ProjectionPredicate),
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct TraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct ProjectionPredicate {
    pub projection_ty: AliasTy,
    pub term: Ty,
}
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct FnSig {
    pub(crate) inputs_and_output: List<Ty>,
}

pub type PolyFnSig = Binder<FnSig>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Ty(Interned<TyS>);

#[derive(Debug, Eq, PartialEq, Hash, Clone, TyEncodable, TyDecodable)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDefData {
    pub did: DefId,
    variants: IndexVec<VariantIdx, VariantDef>,
    flags: AdtFlags,
}

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct VariantDef {
    pub def_id: DefId,
    pub name: Symbol,
    pub fields: IndexVec<FieldIdx, FieldDef>,
}

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct FieldDef {
    pub did: DefId,
    pub name: Symbol,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct TyS {
    kind: TyKind,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    Adt(AdtDef, GenericArgs),
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
    FnPtr(PolyFnSig),
    Closure(DefId, GenericArgs),
    Coroutine(DefId, GenericArgs),
    CoroutineWitness(DefId, GenericArgs),
    Alias(AliasKind, AliasTy),
    RawPtr(Ty, Mutability),
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct AliasTy {
    pub args: GenericArgs,
    pub def_id: DefId,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum AliasKind {
    Projection,
    Opaque,
}

#[derive(Clone, PartialEq, Eq, Hash, Encodable, Decodable, Debug)]
pub struct ValueConst {
    pub val: usize,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Const {
    Param(ParamConst),
    Value(ValueConst),
}

impl From<usize> for Const {
    fn from(val: usize) -> Self {
        Const::Value(ValueConst { val })
    }
}

#[derive(PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Region),
    Const(Const),
}

pub type GenericArgs = List<GenericArg>;

impl GenericArgs {
    pub fn as_closure(&self) -> ClosureArgs {
        ClosureArgs { args: self.clone() }
    }

    pub fn as_generator(&self) -> GeneratorArgs {
        GeneratorArgs { args: self.clone() }
    }
}
pub struct GeneratorArgs {
    pub args: GenericArgs,
}

pub struct ClosureArgs {
    pub args: GenericArgs,
}

#[allow(unused)]
pub struct ClosureArgsParts<'a, T> {
    parent_args: &'a [T],
    closure_kind_ty: &'a T,
    closure_sig_as_fn_ptr_ty: &'a T,
    tupled_upvars_ty: &'a T,
}

#[derive(Debug)]
pub struct GeneratorArgsParts<'a, T> {
    pub parent_args: &'a [T],
    pub resume_ty: &'a T,
    pub yield_ty: &'a T,
    pub return_ty: &'a T,
    pub witness: &'a T,
    pub tupled_upvars_ty: &'a T,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Region {
    ReLateBound(DebruijnIndex, BoundRegion),
    ReEarlyBound(EarlyBoundRegion),
    ReStatic,
    ReVar(RegionVid),
    ReFree(FreeRegion),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct FreeRegion {
    pub scope: DefId,
    pub bound_region: BoundRegionKind,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

impl Generics<'_> {
    pub fn parent(&self) -> Option<DefId> {
        self.orig.parent
    }

    pub fn parent_count(&self) -> usize {
        self.orig.parent_count
    }
}

impl Clause {
    pub(crate) fn new(kind: ClauseKind) -> Clause {
        Clause { kind }
    }
}

impl<T> EarlyBinder<T> {
    pub fn skip_binder(self) -> T {
        self.0
    }

    pub fn instantiate_identity(self) -> T {
        self.0
    }
}

impl EarlyBinder<Ty> {
    pub fn subst(&self, args: &[GenericArg]) -> Ty {
        self.0.subst(args)
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

impl GenericArg {
    pub fn expect_type(&self) -> &Ty {
        if let GenericArg::Ty(ty) = self {
            ty
        } else {
            bug!("expected `GenericArg::Ty`, found {:?}", self)
        }
    }

    fn expect_lifetime(&self) -> Region {
        if let GenericArg::Lifetime(re) = self {
            *re
        } else {
            bug!("expected `GenericArg::Lifetime`, found {:?}", self)
        }
    }

    fn expect_const(&self) -> &Const {
        if let GenericArg::Const(c) = self {
            c
        } else {
            bug!("expected `GenericArg::Const`, found {:?}", self)
        }
    }
}

impl GeneratorArgs {
    pub fn tupled_upvars_ty(&self) -> &Ty {
        self.split().tupled_upvars_ty.expect_type()
    }

    pub fn upvar_tys(&self) -> impl Iterator<Item = &Ty> {
        self.tupled_upvars_ty().tuple_fields().iter()
    }

    fn split(&self) -> GeneratorArgsParts<GenericArg> {
        match &self.args[..] {
            [ref parent_args @ .., resume_ty, yield_ty, return_ty, witness, tupled_upvars_ty] => {
                GeneratorArgsParts {
                    parent_args,
                    resume_ty,
                    yield_ty,
                    return_ty,
                    witness,
                    tupled_upvars_ty,
                }
            }
            _ => bug!("generator args missing synthetics"),
        }
    }
}

impl ClosureArgs {
    pub fn tupled_upvars_ty(&self) -> &Ty {
        self.split().tupled_upvars_ty.expect_type()
    }

    pub fn upvar_tys(&self) -> &List<Ty> {
        self.tupled_upvars_ty().tuple_fields()
    }

    pub fn split(&self) -> ClosureArgsParts<GenericArg> {
        match &self.args[..] {
            [parent_args @ .., closure_kind_ty, closure_sig_as_fn_ptr_ty, tupled_upvars_ty] => {
                ClosureArgsParts {
                    parent_args,
                    closure_kind_ty,
                    closure_sig_as_fn_ptr_ty,
                    tupled_upvars_ty,
                }
            }
            _ => bug!("closure args missing synthetics"),
        }
    }
}

impl AdtDef {
    pub(crate) fn new(data: AdtDefData) -> Self {
        Self(Interned::new(data))
    }

    pub fn did(&self) -> DefId {
        self.0.did
    }

    pub fn flags(&self) -> AdtFlags {
        self.0.flags
    }

    pub fn is_struct(&self) -> bool {
        self.flags().contains(AdtFlags::IS_STRUCT)
    }

    pub fn is_union(&self) -> bool {
        self.flags().contains(AdtFlags::IS_UNION)
    }

    pub fn is_enum(&self) -> bool {
        self.flags().contains(AdtFlags::IS_ENUM)
    }

    pub fn is_box(&self) -> bool {
        self.flags().contains(AdtFlags::IS_BOX)
    }

    pub fn variant(&self, idx: VariantIdx) -> &VariantDef {
        &self.0.variants[idx]
    }

    pub fn variants(&self) -> &IndexSlice<VariantIdx, VariantDef> {
        &self.0.variants
    }

    pub fn non_enum_variant(&self) -> &VariantDef {
        assert!(self.is_struct() || self.is_union());
        self.variant(FIRST_VARIANT)
    }
}

impl AdtDefData {
    pub(crate) fn new(
        did: DefId,
        variants: IndexVec<VariantIdx, VariantDef>,
        flags: AdtFlags,
    ) -> Self {
        Self { did, variants, flags }
    }
}

impl TraitRef {
    pub fn self_ty(&self) -> &Ty {
        self.args[0].expect_type()
    }
}

impl AliasTy {
    /// This method work only with associated type projections (i.e., no opaque tpes)
    pub fn self_ty(&self) -> &Ty {
        self.args[0].expect_type()
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Ty(Interned::new(TyS { kind: self }))
    }
}

impl Ty {
    pub fn mk_adt(adt_def: AdtDef, args: impl Into<GenericArgs>) -> Ty {
        let args = args.into();
        TyKind::Adt(adt_def, args).intern()
    }

    pub fn mk_closure(def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        TyKind::Closure(def_id, args.into()).intern()
    }

    pub fn mk_coroutine(def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        TyKind::Coroutine(def_id, args.into()).intern()
    }

    pub fn mk_generator_witness(def_id: DefId, args: GenericArgs) -> Ty {
        TyKind::CoroutineWitness(def_id, args).intern()
    }

    pub fn mk_alias(kind: AliasKind, def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        let alias_ty = AliasTy { args: args.into(), def_id };
        TyKind::Alias(kind, alias_ty).intern()
    }

    pub fn mk_array(ty: Ty, c: Const) -> Ty {
        TyKind::Array(ty, c).intern()
    }

    pub fn mk_slice(ty: Ty) -> Ty {
        TyKind::Slice(ty).intern()
    }

    pub fn mk_fn_ptr(fn_sig: PolyFnSig) -> Ty {
        TyKind::FnPtr(fn_sig).intern()
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

    pub fn deref(&self) -> Ty {
        match self.kind() {
            TyKind::Adt(adt_def, args) if adt_def.is_box() => args[0].expect_type().clone(),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => ty.clone(),
            _ => bug!("deref projection of non-dereferenceable ty `{self:?}`"),
        }
    }

    pub fn kind(&self) -> &TyKind {
        &self.0.kind
    }

    pub fn tuple_fields(&self) -> &List<Ty> {
        match self.kind() {
            TyKind::Tuple(tys) => tys,
            _ => bug!("tuple_fields called on non-tuple"),
        }
    }

    pub fn expect_adt(&self) -> (&AdtDef, &GenericArgs) {
        match self.kind() {
            TyKind::Adt(adt_def, args) => (adt_def, args),
            _ => bug!("expect_adt called on non-adt"),
        }
    }

    pub fn is_mut_ref(&self) -> bool {
        matches!(self.kind(), TyKind::Ref(.., Mutability::Mut))
    }

    pub fn is_box(&self) -> bool {
        matches!(self.kind(), TyKind::Adt(adt, ..) if adt.is_box())
    }
}

impl_internable!(TyS, AdtDefData);
impl_slice_internable!(Ty, GenericArg, GenericParamDef, BoundVariableKind, Clause);

impl fmt::Debug for GenericArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericArg::Ty(ty) => write!(f, "{ty:?}"),
            GenericArg::Lifetime(region) => write!(f, "{region:?}"),
            GenericArg::Const(c) => write!(f, "Const({c:?})"),
        }
    }
}

impl fmt::Debug for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", region_to_string(*self))
    }
}

impl<T: fmt::Debug> fmt::Debug for Binder<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.1.is_empty() {
            write!(f, "for<{:?}> ", self.1.iter().format(", "))?;
        }
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Debug for FnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn({:?}) -> {:?}", self.inputs().iter().format(", "), self.output())
    }
}

impl fmt::Debug for AliasKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AliasKind::Projection => write!(f, "Projection"),
            AliasKind::Opaque => write!(f, "Opaque"),
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Adt(adt_def, args) => {
                let adt_name = rustc_middle::ty::tls::with(|tcx| {
                    let path = tcx.def_path(adt_def.did());
                    path.data.iter().join("::")
                });
                write!(f, "{adt_name}")?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
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
            TyKind::FnPtr(fn_sig) => write!(f, "{fn_sig:?}"),
            TyKind::Closure(did, args) => {
                write!(f, "Closure {}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::Coroutine(did, args) => {
                write!(f, "Generator {}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::CoroutineWitness(did, args) => {
                write!(f, "GeneratorWitness {}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::Alias(kind, alias_ty) => {
                let def_id = alias_ty.def_id;
                let args = &alias_ty.args;
                write!(f, "Alias ({kind:?}, {}, ", def_id_to_string(def_id))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::Param(param_const) => write!(f, "{:?}", param_const),
            Const::Value(value_const) => write!(f, "{:?}", value_const),
        }
    }
}

pub(crate) fn region_to_string(region: Region) -> String {
    match region {
        Region::ReLateBound(_, region) => {
            match region.kind {
                BoundRegionKind::BrAnon => "'<annon>".to_string(),
                BoundRegionKind::BrNamed(_, sym) => {
                    if sym == kw::UnderscoreLifetime {
                        format!("{sym}{:?}", region.var)
                    } else {
                        format!("{sym}")
                    }
                }
                BoundRegionKind::BrEnv => "'<env>".to_string(),
            }
        }
        Region::ReEarlyBound(region) => region.name.to_string(),
        Region::ReStatic => "'static".to_string(),
        Region::ReVar(rvid) => format!("{rvid:?}"),
        Region::ReFree(..) => "'<free>".to_string(),
    }
}
