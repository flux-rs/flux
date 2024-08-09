#![feature(
    associated_type_defaults,
    box_patterns,
    if_let_guard,
    let_chains,
    min_specialization,
    never_type,
    rustc_private,
    unwrap_infallible
)]

//! This crate contains common type definitions that are used by other crates.

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
pub mod intern;
pub mod pretty;
pub mod queries;
pub mod rty;
pub mod rustc;
mod sort_of;

use std::sync::LazyLock;

use flux_config as config;
use flux_macros::fluent_messages;
use flux_syntax::surface::{self, NodeId};
use intern::List;
use rustc_data_structures::unord::UnordMap;
use rustc_hash::FxHashSet;
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
    pub qualifs: Vec<surface::Qualifier>,
    pub func_defs: Vec<surface::SpecFunc>,
    pub sort_decls: Vec<surface::SortDecl>,
    pub ty_aliases: UnordMap<OwnerId, Option<surface::TyAlias>>,
    pub ignores: UnordMap<LocalDefId, fhir::Ignored>,
    pub trusted: UnordMap<LocalDefId, fhir::Trusted>,
    pub consts: FxHashSet<LocalDefId>,
    pub crate_config: Option<config::CrateConfig>,
    extern_id_to_local_id: UnordMap<DefId, LocalDefId>,
    local_id_to_extern_id: UnordMap<LocalDefId, DefId>,
}

impl Specs {
    pub fn extend_items(&mut self, items: impl IntoIterator<Item = surface::Item>) {
        for item in items {
            match item {
                surface::Item::Qualifier(qualifier) => self.qualifs.push(qualifier),
                surface::Item::FuncDef(defn) => self.func_defs.push(defn),
                surface::Item::SortDecl(sort_decl) => self.sort_decls.push(sort_decl),
            }
        }
    }

    pub fn insert_extern_id(&mut self, local_id: LocalDefId, extern_id: DefId) {
        self.extern_id_to_local_id.insert(extern_id, local_id);
        self.local_id_to_extern_id.insert(local_id, extern_id);
    }
}

#[derive(Default)]
pub struct ResolverOutput {
    pub path_res_map: UnordMap<NodeId, fhir::PartialRes>,
    pub impl_trait_res_map: UnordMap<NodeId, hir::ItemId>,
    /// Resolution of explicit and implicit parameters. The [`fhir::ParamId`] is unique per item.
    /// The [`NodeId`] used as the key corresponds to the node introducing the parameter. When explicit,
    /// this is the id of the [`surface::GenericArg`] or [`surface::RefineParam`], when implicit, this
    /// is the id of the [`surface::RefineArg::Bind`] or [`surface::FnInput`].
    pub param_res_map: UnordMap<NodeId, (fhir::ParamId, fhir::ParamKind)>,
    /// List of implicit params defined in a scope. The [`NodeId`] used as key is the id of the node
    /// introducing the scope, e.g., [`surface::FnSig`], [`surface::FnOutput`], or [`surface::VariantDef`].
    /// The [`NodeId`]s in the vectors are keys in [`Self::param_res_map`].
    pub implicit_params: UnordMap<NodeId, Vec<(Ident, NodeId)>>,
    pub sort_path_res_map: UnordMap<NodeId, fhir::SortRes>,
    pub path_expr_res_map: UnordMap<NodeId, fhir::ExprRes>,
}
