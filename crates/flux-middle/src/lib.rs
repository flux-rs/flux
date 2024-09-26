//! This crate contains common type definitions that are used by other crates.

#![feature(
    associated_type_defaults,
    box_patterns,
    closure_track_caller,
    if_let_guard,
    let_chains,
    min_specialization,
    never_type,
    precise_capturing,
    rustc_private,
    unwrap_infallible
)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

extern crate self as flux_middle;

pub mod big_int;
pub mod cstore;
pub mod fhir;
pub mod global_env;
pub mod pretty;
pub mod queries;
pub mod rty;
mod sort_of;

use std::sync::LazyLock;

use flux_arc_interner::List;
use flux_config as config;
use flux_macros::fluent_messages;
pub use flux_rustc_bridge::def_id_to_string;
use flux_rustc_bridge::{
    mir::{LocalDecls, PlaceElem},
    ty::{self, GenericArgsExt},
};
use flux_syntax::surface::{self, NodeId};
use global_env::GlobalEnv;
use queries::QueryResult;
use rty::VariantIdx;
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{UnordMap, UnordSet},
};
use rustc_hir as hir;
use rustc_hir::OwnerId;
use rustc_macros::extension;
use rustc_span::{
    def_id::{DefId, LocalDefId},
    symbol::Ident,
    Symbol,
};
use rustc_target::abi::FieldIdx;

fluent_messages! { "../locales/en-US.ftl" }

pub struct TheoryFunc {
    pub name: Symbol,
    pub sort: rty::PolyFuncSort,
    pub fixpoint_name: Symbol,
}

pub static THEORY_FUNCS: LazyLock<UnordMap<Symbol, TheoryFunc>> = LazyLock::new(|| {
    use rty::{
        BvSize, ParamSort,
        Sort::{self, *},
        SortCtor::*,
        SortParamKind,
    };
    let param0 = ParamSort::from_u32(0);
    let param1 = ParamSort::from_u32(1);
    let bv_param0 = BvSize::Param(ParamSort::from_u32(0));
    [
        // String operations
        TheoryFunc {
            name: Symbol::intern("str_len"),
            fixpoint_name: Symbol::intern("strLen"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Str], Int),
            ),
        },
        // BitVector <-> int
        TheoryFunc {
            name: Symbol::intern("bv_zero_extend_32_to_64"),
            fixpoint_name: Symbol::intern("app (_ zero_extend 32)"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(32))], BitVec(BvSize::Fixed(64))),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_sign_extend_32_to_64"),
            fixpoint_name: Symbol::intern("app (_ sign_extend 32)"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(32))], BitVec(BvSize::Fixed(64))),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_int_to_bv32"),
            fixpoint_name: Symbol::intern("int_to_bv32"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Int], BitVec(BvSize::Fixed(32))),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_bv32_to_int"),
            fixpoint_name: Symbol::intern("bv32_to_int"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(32))], Int),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_int_to_bv64"),
            fixpoint_name: Symbol::intern("int_to_bv64"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![rty::Sort::Int], BitVec(BvSize::Fixed(64))),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_bv64_to_int"),
            fixpoint_name: Symbol::intern("bv64_to_int"),
            sort: rty::PolyFuncSort::new(
                List::empty(),
                rty::FuncSort::new(vec![BitVec(BvSize::Fixed(64))], Int),
            ),
        },
        // BitVector arith
        TheoryFunc {
            name: Symbol::intern("bv_add"),
            fixpoint_name: Symbol::intern("bvadd"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_neg"),
            fixpoint_name: Symbol::intern("bvneg"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_sub"),
            fixpoint_name: Symbol::intern("bvsub"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_shl"),
            fixpoint_name: Symbol::intern("bvshl"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_lshr"),
            fixpoint_name: Symbol::intern("bvlshr"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_ashr"),
            fixpoint_name: Symbol::intern("bvashr"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_mul"),
            fixpoint_name: Symbol::intern("bvmul"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_udiv"),
            fixpoint_name: Symbol::intern("bvudiv"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_urem"),
            fixpoint_name: Symbol::intern("bvurem"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_sdiv"),
            fixpoint_name: Symbol::intern("bvsdiv"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_srem"),
            fixpoint_name: Symbol::intern("bvsrem"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_smod"),
            fixpoint_name: Symbol::intern("bvsmod"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        // BitVector bitwise
        TheoryFunc {
            name: Symbol::intern("bv_and"),
            fixpoint_name: Symbol::intern("bvand"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_or"),
            fixpoint_name: Symbol::intern("bvor"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_xor"),
            fixpoint_name: Symbol::intern("bvxor"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0), BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("bv_not"),
            fixpoint_name: Symbol::intern("bvnot"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::BvSize),
                rty::FuncSort::new(vec![BitVec(bv_param0)], BitVec(bv_param0)),
            ),
        },
        // Set operations
        TheoryFunc {
            name: Symbol::intern("set_empty"),
            fixpoint_name: Symbol::intern("Set_empty"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(vec![Int], Sort::app(Set, List::singleton(Var(param0)))),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("set_singleton"),
            fixpoint_name: Symbol::intern("Set_sng"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(vec![Var(param0)], Sort::app(Set, List::singleton(Var(param0)))),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("set_union"),
            fixpoint_name: Symbol::intern("Set_cup"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(
                    vec![
                        Sort::app(Set, List::singleton(Var(param0))),
                        Sort::app(Set, List::singleton(Var(param0))),
                    ],
                    Sort::app(Set, List::singleton(Var(param0))),
                ),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("set_is_in"),
            fixpoint_name: Symbol::intern("Set_mem"),
            sort: rty::PolyFuncSort::new(
                List::singleton(SortParamKind::Sort),
                rty::FuncSort::new(
                    vec![Var(param0), Sort::app(Set, List::singleton(Var(param0)))],
                    Bool,
                ),
            ),
        },
        // Map operations
        TheoryFunc {
            name: Symbol::intern("map_default"),
            fixpoint_name: Symbol::intern("Map_default"),
            sort: rty::PolyFuncSort::new(
                List::from_arr([SortParamKind::Sort, SortParamKind::Sort]),
                rty::FuncSort::new(
                    vec![Var(param1)],
                    Sort::app(Map, List::from_arr([Var(param0), Var(param1)])),
                ),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("map_select"),
            fixpoint_name: Symbol::intern("Map_select"),
            sort: rty::PolyFuncSort::new(
                List::from_arr([SortParamKind::Sort, SortParamKind::Sort]),
                rty::FuncSort::new(
                    vec![Sort::app(Map, List::from_arr([Var(param0), Var(param1)])), Var(param0)],
                    Var(param1),
                ),
            ),
        },
        TheoryFunc {
            name: Symbol::intern("map_store"),
            fixpoint_name: Symbol::intern("Map_store"),
            sort: rty::PolyFuncSort::new(
                List::from_arr([SortParamKind::Sort, SortParamKind::Sort]),
                rty::FuncSort::new(
                    vec![
                        Sort::app(Map, List::from_arr([Var(param0), Var(param1)])),
                        Var(param0),
                        Var(param1),
                    ],
                    Sort::app(Map, List::from_arr([Var(param0), Var(param1)])),
                ),
            ),
        },
    ]
    .into_iter()
    .map(|itf| (itf.name, itf))
    .collect()
});

#[derive(Default)]
pub struct Specs {
    pub fn_sigs: UnordMap<OwnerId, surface::FnSpec>,
    pub structs: UnordMap<OwnerId, surface::StructDef>,
    pub traits: UnordMap<OwnerId, surface::Trait>,
    pub impls: UnordMap<OwnerId, surface::Impl>,
    pub enums: UnordMap<OwnerId, surface::EnumDef>,
    pub flux_items_by_parent: FxIndexMap<OwnerId, Vec<surface::Item>>,
    pub ty_aliases: UnordMap<OwnerId, Option<surface::TyAlias>>,
    pub ignores: UnordMap<LocalDefId, fhir::Ignored>,
    pub trusted: UnordMap<LocalDefId, fhir::Trusted>,
    pub crate_config: Option<config::CrateConfig>,
    pub should_fail: UnordSet<LocalDefId>,
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
    pub fn insert_extern_id(&mut self, local_id: LocalDefId, extern_id: DefId) {
        self.extern_id_to_local_id.insert(extern_id, local_id);
        self.local_id_to_extern_id.insert(local_id, extern_id);
    }

    pub fn insert_dummy(&mut self, owner_id: OwnerId) {
        self.dummy_extern.insert(owner_id.def_id);
    }
}

#[derive(Default)]
pub struct ResolverOutput {
    pub path_res_map: UnordMap<NodeId, fhir::PartialRes>,
    pub impl_trait_res_map: UnordMap<NodeId, hir::ItemId>,
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
    pub expr_path_res_map: UnordMap<NodeId, fhir::ExprRes>,
}

/// This enum serves as a type-level reminder that local ids can wrap an extern specs. The
/// abstraction is not infallible, so one should still be careful and decide in each situation
/// whether to use the [_local id_] or the [_resolved id_]. Although the construction of
/// [`MaybeExternId`] is not encapsulated, it is recommended to use [`GlobalEnv::maybe_extern_id`]
/// to create one.
///
/// The enum is generic on the local `Id` as we use it with various kinds of local ids, e.g.,
/// [`LocalDefId`], [`OwnerId`], ...
///
/// [_local id_]: MaybeExternId::local_id
/// [_resolved id_]: MaybeExternId::resolved_id
/// [`GlobalEnv::maybe_extern_id`]: crate::global_env::GlobalEnv::maybe_extern_id
#[derive(Clone, Copy, Debug)]
pub enum MaybeExternId<Id = LocalDefId> {
    /// An id for a local spec.
    Local(Id),
    /// An id wrapping an external spec. The `Id` is the local id of item holding the extern spec. The
    /// `DefId` is the resolved id for the external item.
    Extern(Id, DefId),
}

impl<Id> MaybeExternId<Id> {
    pub fn map<R>(self, f: impl FnOnce(Id) -> R) -> MaybeExternId<R> {
        match self {
            MaybeExternId::Local(local_id) => MaybeExternId::Local(f(local_id)),
            MaybeExternId::Extern(local_id, def_id) => MaybeExternId::Extern(f(local_id), def_id),
        }
    }

    pub fn local_id(self) -> Id {
        match self {
            MaybeExternId::Local(local_id) | MaybeExternId::Extern(local_id, _) => local_id,
        }
    }

    /// Returns `true` if the maybe extern id is [`Local`].
    ///
    /// [`Local`]: MaybeExternId::Local
    #[must_use]
    pub fn is_local(self) -> bool {
        matches!(self, Self::Local(..))
    }

    /// Returns `true` if the maybe extern id is [`Extern`].
    ///
    /// [`Extern`]: MaybeExternId::Extern
    #[must_use]
    pub fn is_extern(&self) -> bool {
        matches!(self, Self::Extern(..))
    }

    pub fn as_local(self) -> Option<Id> {
        if let MaybeExternId::Local(local_id) = self {
            Some(local_id)
        } else {
            None
        }
    }

    pub fn as_extern(self) -> Option<DefId> {
        if let MaybeExternId::Extern(_, def_id) = self {
            Some(def_id)
        } else {
            None
        }
    }
}

impl<Id: Into<DefId>> MaybeExternId<Id> {
    /// Returns the [`DefId`] this id _truly_ corresponds to, i.e, returns the [`DefId`] of the
    /// extern item if [`Extern`] or converts the local id into a [`DefId`] if [`Local`].
    ///
    /// [`Local`]: MaybeExternId::Local
    /// [`Extern`]: MaybeExternId::Extern
    pub fn resolved_id(self) -> DefId {
        match self {
            MaybeExternId::Local(local_id) => local_id.into(),
            MaybeExternId::Extern(_, def_id) => def_id,
        }
    }
}

impl rustc_middle::query::IntoQueryParam<DefId> for MaybeExternId {
    fn into_query_param(self) -> DefId {
        self.resolved_id()
    }
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
