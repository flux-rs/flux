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

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
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

pub mod const_eval;
pub mod cstore;
pub mod fhir;
pub mod global_env;
pub mod pretty;
pub mod queries;
pub mod rty;
pub mod rustc;
mod sort_of;

use std::sync::LazyLock;

use flux_arc_interner::List;
use flux_config as config;
use flux_macros::fluent_messages;
use flux_syntax::surface::{self, NodeId};
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{UnordMap, UnordSet},
};
use rustc_hir as hir;
use rustc_hir::OwnerId;
use rustc_span::{
    def_id::{DefId, LocalDefId},
    symbol::Ident,
    Symbol,
};

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
    let param0 = ParamSort::from(0);
    let param1 = ParamSort::from(1);
    let bv_param0 = BvSize::Param(ParamSort::from(0));
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

/// This enum serves as a type-level reminder that local ids can refer to extern specs. The
/// abstraction is not infallible, so one shoud still be careful and decide in each situation
/// whether to use the [_local id_] or the [_resolved id_]. Although the construction of
/// [`MaybeExternId`] is not encapsulated, it is recommened to use [`GlobalEnv::maybe_extern_id`]
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
    /// An id for an external spec. The `Id` is the local id of item holding the extern spec. The
    /// `Defid` is the resolved id for the external item.
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
    /// Returns the [`DefId`] this id _trully_ corresponds to, i.e, returns the [`DefId`] of the
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
