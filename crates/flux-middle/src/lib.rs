//! This crate contains common type definitions that are used by other crates.
#![feature(
    associated_type_defaults,
    box_patterns,
    closure_track_caller,
    if_let_guard,
    map_try_insert,
    min_specialization,
    never_type,
    rustc_private,
    unwrap_infallible,
    new_range_api
)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_type_ir;

extern crate self as flux_middle;

pub mod big_int;
pub mod cstore;
pub mod def_id;
pub mod fhir;
pub mod global_env;
pub mod metrics;
pub mod pretty;
pub mod queries;
pub mod rty;
mod sort_of;

use std::sync::LazyLock;

use flux_arc_interner::List;
use flux_macros::fluent_messages;
pub use flux_rustc_bridge::def_id_to_string;
use flux_rustc_bridge::{
    mir::{LocalDecls, PlaceElem},
    ty::{self, GenericArgsExt},
};
use flux_syntax::surface::{self, NodeId};
use global_env::GlobalEnv;
use liquid_fixpoint::ThyFunc;
use queries::QueryResult;
use rty::VariantIdx;
use rustc_abi::FieldIdx;
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{UnordMap, UnordSet},
};
use rustc_hir::OwnerId;
use rustc_macros::extension;
use rustc_middle::ty::TyCtxt;
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
    symbol::Ident,
};

fluent_messages! { "../locales/en-US.ftl" }

pub struct TheoryFunc {
    pub name: Symbol,
    pub sort: rty::PolyFuncSort,
    pub itf: liquid_fixpoint::ThyFunc,
}

pub static THEORY_FUNCS: LazyLock<UnordMap<liquid_fixpoint::ThyFunc, TheoryFunc>> =
    LazyLock::new(|| {
        use rty::{BvSize, Sort::*};
        liquid_fixpoint::ThyFunc::ALL
            .into_iter()
            .filter_map(|func| {
                let func = TheoryFunc {
                    name: Symbol::intern(name_of_thy_func(func)?),
                    itf: func,
                    sort: sort_of_thy_func(func)?,
                };
                Some(func)
            })
            .chain([
                // we can't express these as function types so we add special case
                TheoryFunc {
                    name: Symbol::intern("bv_zero_extend_32_to_64"),
                    itf: liquid_fixpoint::ThyFunc::BvZeroExtend(32),
                    sort: rty::PolyFuncSort::new(
                        List::empty(),
                        rty::FuncSort::new(
                            vec![BitVec(BvSize::Fixed(32))],
                            BitVec(BvSize::Fixed(64)),
                        ),
                    ),
                },
                TheoryFunc {
                    name: Symbol::intern("bv_sign_extend_32_to_64"),
                    itf: liquid_fixpoint::ThyFunc::BvSignExtend(32),
                    sort: rty::PolyFuncSort::new(
                        List::empty(),
                        rty::FuncSort::new(
                            vec![BitVec(BvSize::Fixed(32))],
                            BitVec(BvSize::Fixed(64)),
                        ),
                    ),
                },
            ])
            .map(|func| (func.itf, func))
            .collect()
    });

pub fn name_of_thy_func(func: liquid_fixpoint::ThyFunc) -> Option<&'static str> {
    let name = match func {
        ThyFunc::BvZeroExtend(_) | ThyFunc::BvSignExtend(_) => return None,
        ThyFunc::StrLen => "str_len",
        ThyFunc::StrConcat => "str_concat",
        ThyFunc::StrPrefixOf => "str_prefix_of",
        ThyFunc::StrSuffixOf => "str_suffix_of",
        ThyFunc::StrContains => "str_contains",
        ThyFunc::IntToBv8 => "bv_int_to_bv8",
        ThyFunc::Bv8ToInt => "bv_bv8_to_int",
        ThyFunc::IntToBv32 => "bv_int_to_bv32",
        ThyFunc::Bv32ToInt => "bv_bv32_to_int",
        ThyFunc::IntToBv64 => "bv_int_to_bv64",
        ThyFunc::Bv64ToInt => "bv_bv64_to_int",
        ThyFunc::BvUge => "bv_uge",
        ThyFunc::BvSge => "bv_sge",
        ThyFunc::BvUdiv => "bv_udiv",
        ThyFunc::BvSdiv => "bv_sdiv",
        ThyFunc::BvSrem => "bv_srem",
        ThyFunc::BvUrem => "bv_urem",
        ThyFunc::BvLshr => "bv_lshr",
        ThyFunc::BvAshr => "bv_ashr",
        ThyFunc::BvAnd => "bv_and",
        ThyFunc::BvOr => "bv_or",
        ThyFunc::BvXor => "bv_xor",
        ThyFunc::BvNot => "bv_not",
        ThyFunc::BvAdd => "bv_add",
        ThyFunc::BvNeg => "bv_neg",
        ThyFunc::BvSub => "bv_sub",
        ThyFunc::BvMul => "bv_mul",
        ThyFunc::BvShl => "bv_shl",
        ThyFunc::BvUle => "bv_ule",
        ThyFunc::BvSle => "bv_sle",
        ThyFunc::BvUgt => "bv_ugt",
        ThyFunc::BvSgt => "bv_sgt",
        ThyFunc::BvUlt => "bv_ult",
        ThyFunc::BvSlt => "bv_slt",
        ThyFunc::SetEmpty => "set_empty",
        ThyFunc::SetSng => "set_singleton",
        ThyFunc::SetCup => "set_union",
        ThyFunc::SetCap => "set_intersection",
        ThyFunc::SetDif => "set_difference",
        ThyFunc::SetSub => "set_subset",
        ThyFunc::SetMem => "set_is_in",
        ThyFunc::MapDefault => "map_default",
        ThyFunc::MapSelect => "map_select",
        ThyFunc::MapStore => "map_store",
    };
    Some(name)
}

fn sort_of_thy_func(func: liquid_fixpoint::ThyFunc) -> Option<rty::PolyFuncSort> {
    use rty::{
        BvSize, ParamSort,
        Sort::{self, *},
        SortCtor::*,
        SortParamKind,
    };
    let param0 = ParamSort::from_u32(0);
    let param1 = ParamSort::from_u32(1);
    let bv_param0 = BvSize::Param(ParamSort::from_u32(0));

    let sort = match func {
        ThyFunc::BvZeroExtend(_) | ThyFunc::BvSignExtend(_) => return None,
        ThyFunc::StrLen => {
            // str -> int
            rty::PolyFuncSort::new(List::empty(), rty::FuncSort::new(vec![rty::Sort::Str], Int))
        }
        ThyFunc::StrConcat => {
            // (str, str) -> str
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Str, rty::Sort::Str], rty::Sort::Str),
            )
        }
        ThyFunc::StrPrefixOf | ThyFunc::StrSuffixOf | ThyFunc::StrContains => {
            // (str, str) -> bool
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Str, rty::Sort::Str], Bool),
            )
        }
        ThyFunc::IntToBv8 => {
            // int -> BitVec<8>
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Int], BitVec(BvSize::Fixed(8))),
            )
        }
        ThyFunc::Bv8ToInt => {
            // BitVec<8> -> int
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(8))], Int),
            )
        }
        ThyFunc::IntToBv32 => {
            // int -> BitVec<32>
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Int], BitVec(BvSize::Fixed(32))),
            )
        }
        ThyFunc::Bv32ToInt => {
            // BitVec<32> -> int
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(32))], Int),
            )
        }
        ThyFunc::IntToBv64 => {
            // int -> BitVec<64>
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Int], BitVec(BvSize::Fixed(64))),
            )
        }
        ThyFunc::Bv64ToInt => {
            // BitVec<64> -> int
            rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(64))], Int),
            )
        }
        ThyFunc::BvUdiv
        | ThyFunc::BvSdiv
        | ThyFunc::BvSrem
        | ThyFunc::BvUrem
        | ThyFunc::BvLshr
        | ThyFunc::BvAshr
        | ThyFunc::BvAnd
        | ThyFunc::BvOr
        | ThyFunc::BvXor
        | ThyFunc::BvAdd
        | ThyFunc::BvSub
        | ThyFunc::BvMul
        | ThyFunc::BvShl => {
            // ∀s. (BitVec<s>, BitVec<s>) -> BitVec<s>
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            )
        }
        ThyFunc::BvNot | ThyFunc::BvNeg => {
            // ∀s. BitVec<s> -> BitVec<s>
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0)], BitVec(bv_param0)),
            )
        }
        ThyFunc::BvUgt
        | ThyFunc::BvSgt
        | ThyFunc::BvUlt
        | ThyFunc::BvSlt
        | ThyFunc::BvSle
        | ThyFunc::BvUge
        | ThyFunc::BvSge
        | ThyFunc::BvUle => {
            // ∀s. (BitVec<s>, BitVec<s>) -> bool
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], Bool),
            )
        }
        ThyFunc::SetEmpty => {
            // ∀s. int -> Set<S> why does this take an int?
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(vec![Int], Sort::app(Set, List::singleton(Var(param0)))),
            )
        }
        ThyFunc::SetSng => {
            // ∀s. s -> Set<S>
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(vec![Var(param0)], Sort::app(Set, List::singleton(Var(param0)))),
            )
        }
        ThyFunc::SetCup | ThyFunc::SetCap | ThyFunc::SetDif => {
            // ∀s. (Set<S>, Set<S>) -> Set<S>
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(
                    vec![
                        Sort::app(Set, List::singleton(Var(param0))),
                        Sort::app(Set, List::singleton(Var(param0))),
                    ],
                    Sort::app(Set, List::singleton(Var(param0))),
                ),
            )
        }
        ThyFunc::SetMem => {
            // ∀s. (s, Set<S>) -> bool
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(
                    vec![Var(param0), Sort::app(Set, List::singleton(Var(param0)))],
                    Bool,
                ),
            )
        }
        ThyFunc::SetSub => {
            // ∀s. (Set<s>, Set<s>) -> bool
            rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(
                    vec![
                        Sort::app(Set, List::singleton(Var(param0))),
                        Sort::app(Set, List::singleton(Var(param0))),
                    ],
                    Bool,
                ),
            )
        }

        ThyFunc::MapDefault => {
            // ∀k,v. v -> Map<k,v>
            rty::PolyFuncSort::new(
                List::from_arr([SortParamKind::Sort, SortParamKind::Sort]),
                rty::FuncSort::new(
                    vec![Var(param1)],
                    Sort::app(Map, List::from_arr([Var(param0), Var(param1)])),
                ),
            )
        }
        ThyFunc::MapSelect => {
            // ∀k,v. (Map<k,v>, k) -> v
            rty::PolyFuncSort::new(
                List::from_arr([SortParamKind::Sort, SortParamKind::Sort]),
                rty::FuncSort::new(
                    vec![Sort::app(Map, List::from_arr([Var(param0), Var(param1)])), Var(param0)],
                    Var(param1),
                ),
            )
        }
        ThyFunc::MapStore => {
            // ∀k,v. (Map<k,v>, k, v) -> Map<k, v>
            rty::PolyFuncSort::new(
                List::from_arr([SortParamKind::Sort, SortParamKind::Sort]),
                rty::FuncSort::new(
                    vec![
                        Sort::app(Map, List::from_arr([Var(param0), Var(param1)])),
                        Var(param0),
                        Var(param1),
                    ],
                    Sort::app(Map, List::from_arr([Var(param0), Var(param1)])),
                ),
            )
        }
    };
    Some(sort)
}

#[derive(Default)]
pub struct Specs {
    items: UnordMap<OwnerId, surface::Item>,
    trait_items: UnordMap<OwnerId, surface::TraitItemFn>,
    impl_items: UnordMap<OwnerId, surface::ImplItemFn>,
    pub flux_items_by_parent: FxIndexMap<OwnerId, Vec<surface::FluxItem>>,
    /// Set of dummy items generated by the extern spec macro we must completely ignore. This is
    /// not the same as [ignored items] because, for ignored items, we still need to return errors
    /// for queries and handle them gracefully in order to report them at the use it.
    ///
    /// If an item is in this set, all its descendants are also consider dummy (but they may not be
    /// in the set).
    ///
    /// [ignored items]: Specs::ignores
    dummy_extern: UnordSet<LocalDefId>,
    extern_id_to_local_id: UnordMap<DefId, LocalDefId>,
    local_id_to_extern_id: UnordMap<LocalDefId, DefId>,
}

impl Specs {
    pub fn insert_extern_spec_id_mapping(
        &mut self,
        local_id: LocalDefId,
        extern_id: DefId,
    ) -> Result<(), ExternSpecMappingErr> {
        #[expect(
            clippy::disallowed_methods,
            reason = "we are inserting the extern spec mapping and we want to ensure it doesn't point to a local item"
        )]
        if let Some(local) = extern_id.as_local() {
            return Err(ExternSpecMappingErr::IsLocal(local));
        }
        if let Err(err) = self.extern_id_to_local_id.try_insert(extern_id, local_id) {
            return Err(ExternSpecMappingErr::Dup(*err.entry.get()));
        }
        self.local_id_to_extern_id.insert(local_id, extern_id);
        Ok(())
    }

    pub fn insert_dummy(&mut self, def_id: LocalDefId) {
        self.dummy_extern.insert(def_id);
    }

    pub fn get_item(&self, owner_id: OwnerId) -> Option<&surface::Item> {
        self.items.get(&owner_id)
    }

    pub fn insert_item(&mut self, owner_id: OwnerId, item: surface::Item) -> Option<surface::Item> {
        if let Some(old) = self.items.insert(owner_id, item) {
            return Some(old);
        }
        None
    }

    pub fn get_trait_item(&self, owner_id: OwnerId) -> Option<&surface::TraitItemFn> {
        self.trait_items.get(&owner_id)
    }

    pub fn insert_trait_item(
        &mut self,
        owner_id: OwnerId,
        trait_item: surface::TraitItemFn,
    ) -> Option<surface::TraitItemFn> {
        if let Some(old) = self.trait_items.insert(owner_id, trait_item) {
            return Some(old);
        }
        None
    }

    pub fn get_impl_item(&self, owner_id: OwnerId) -> Option<&surface::ImplItemFn> {
        self.impl_items.get(&owner_id)
    }

    pub fn insert_impl_item(
        &mut self,
        owner_id: OwnerId,
        impl_item: surface::ImplItemFn,
    ) -> Option<surface::ImplItemFn> {
        if let Some(old) = self.impl_items.insert(owner_id, impl_item) {
            return Some(old);
        }
        None
    }
}

/// Represents errors that can occur when inserting a mapping between a `LocalDefId` and a `DefId`
/// for an extern spec.
pub enum ExternSpecMappingErr {
    /// Indicates that the [`DefId`] we are trying to add extern specs to is actually local. Returns
    /// the [`DefId`] as a [`LocalDefId`].
    IsLocal(LocalDefId),

    /// Indicates that there is an existing extern spec for the given extern id. Returns the existing
    /// `LocalDefId` that maps to the extern id.
    ///
    /// NOTE: This currently only considers extern specs defined in the local crate. There could still
    /// be duplicates if an extern spec is imported from an external crate. In such cases, the local
    /// extern spec takes precedence. Probably, we should at least warn about this, but it's a bit
    /// tricky because we need to look at the crate metadata which we don't have handy when
    /// collecting specs.
    Dup(LocalDefId),
}

#[derive(Default)]
pub struct ResolverOutput {
    pub path_res_map: UnordMap<NodeId, fhir::PartialRes>,
    /// Resolution of explicitly and implicitly scoped parameters. The [`fhir::ParamId`] is unique
    /// per item. The [`NodeId`] used as the key corresponds to the node introducing the parameter.
    /// When explicit, this is the id of the [`surface::GenericArg`] or [`surface::RefineParam`],
    /// when implicit, this is the id of the [`surface::RefineArg::Bind`] or [`surface::FnInput`].
    pub param_res_map: UnordMap<NodeId, (fhir::ParamId, fhir::ParamKind)>,
    /// List of implicitly scoped params defined in a scope. The [`NodeId`] used as key is the id of
    /// the node introducing the scope, e.g., [`surface::FnSig`], [`surface::FnOutput`], or
    /// [`surface::VariantDef`]. The [`NodeId`]s in the vectors are keys in [`Self::param_res_map`].
    pub implicit_params: UnordMap<NodeId, Vec<(Ident, NodeId)>>,
    pub sort_path_res_map: UnordMap<NodeId, fhir::SortRes>,
    pub expr_path_res_map: UnordMap<NodeId, fhir::PartialRes<fhir::ParamId>>,
    /// The resolved list of local qualifiers per function.
    /// The [`NodeId`] corresponds to the [`surface::FnSpec`].
    pub qualifier_res_map: UnordMap<NodeId, Vec<def_id::FluxLocalDefId>>,
    /// The resolved list of local reveals per function
    /// The [`NodeId`] corresponds to the [`surface::FnSpec`].
    pub reveal_res_map: UnordMap<NodeId, Vec<def_id::FluxDefId>>,
}

#[extension(pub trait PlaceExt)]
impl flux_rustc_bridge::mir::Place {
    fn ty(&self, genv: GlobalEnv, local_decls: &LocalDecls) -> QueryResult<PlaceTy> {
        self.projection
            .iter()
            .try_fold(PlaceTy::from_ty(local_decls[self.local].ty.clone()), |place_ty, elem| {
                place_ty.projection_ty(genv, *elem)
            })
    }

    fn behind_raw_ptr(&self, genv: GlobalEnv, local_decls: &LocalDecls) -> QueryResult<bool> {
        let mut place_ty = PlaceTy::from_ty(local_decls[self.local].ty.clone());
        for elem in &self.projection {
            if let (PlaceElem::Deref, ty::TyKind::RawPtr(..)) = (elem, place_ty.ty.kind()) {
                return Ok(true);
            }
            place_ty = place_ty.projection_ty(genv, *elem)?;
        }
        Ok(false)
    }
}

#[derive(Debug)]
pub struct PlaceTy {
    pub ty: ty::Ty,
    /// Downcast to a particular variant of an enum or a generator, if included.
    pub variant_index: Option<VariantIdx>,
}

impl PlaceTy {
    fn from_ty(ty: ty::Ty) -> PlaceTy {
        PlaceTy { ty, variant_index: None }
    }

    fn projection_ty(&self, genv: GlobalEnv, elem: PlaceElem) -> QueryResult<PlaceTy> {
        if self.variant_index.is_some() && !matches!(elem, PlaceElem::Field(..)) {
            Err(query_bug!("cannot use non field projection on downcasted place"))?;
        }
        let place_ty = match elem {
            PlaceElem::Deref => PlaceTy::from_ty(self.ty.deref()),
            PlaceElem::Field(fld) => PlaceTy::from_ty(self.field_ty(genv, fld)?),
            PlaceElem::Downcast(_, variant_idx) => {
                PlaceTy { ty: self.ty.clone(), variant_index: Some(variant_idx) }
            }
            PlaceElem::Index(_) | PlaceElem::ConstantIndex { .. } => {
                if let ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) = self.ty.kind() {
                    PlaceTy::from_ty(ty.clone())
                } else {
                    return Err(query_bug!("cannot use non field projection on downcasted place"));
                }
            }
        };
        Ok(place_ty)
    }

    fn field_ty(&self, genv: GlobalEnv, f: FieldIdx) -> QueryResult<ty::Ty> {
        match self.ty.kind() {
            ty::TyKind::Adt(adt_def, args) => {
                let variant_def = match self.variant_index {
                    None => adt_def.non_enum_variant(),
                    Some(variant_index) => {
                        assert!(adt_def.is_enum());
                        adt_def.variant(variant_index)
                    }
                };
                let field_def = &variant_def.fields[f];
                let ty = genv.lower_type_of(field_def.did)?;
                Ok(ty.subst(args))
            }
            ty::TyKind::Tuple(tys) => Ok(tys[f.index()].clone()),
            ty::TyKind::Closure(_, args) => Ok(args.as_closure().upvar_tys()[f.index()].clone()),
            _ => Err(query_bug!("extracting field of non-tuple non-adt non-closure: {self:?}")),
        }
    }
}

/// The different reasons we issue fixpoint queries. This is used to dissambiguate queries that
/// are issued for the same item.
///
/// NOTE: This is defined here because it's also used in [`metrics`]
#[derive(Debug, Hash, Clone, Copy)]
pub enum FixpointQueryKind {
    /// Query issued when checking an impl method is a subtype of the trait
    Impl,
    /// Query issued to check the body of a function
    Body,
    /// Query issued to check an (enum) invariant is implied by the type definition
    Invariant,
}

impl FixpointQueryKind {
    pub fn ext(self) -> &'static str {
        match self {
            FixpointQueryKind::Impl => "sub.fluxc",
            FixpointQueryKind::Body => "fluxc",
            FixpointQueryKind::Invariant => "fluxc",
        }
    }

    /// A string that uniquely identifies a query given an item `DefId`
    pub fn task_key(self, tcx: TyCtxt, def_id: DefId) -> String {
        format!("{}###{:?}", tcx.def_path_str(def_id), self)
    }

    /// Returns `true` if the fixpoint query kind is [`Body`].
    ///
    /// [`Body`]: FixpointQueryKind::Body
    #[must_use]
    pub fn is_body(&self) -> bool {
        matches!(self, Self::Body)
    }
}
