#![feature(
    associated_type_defaults,
    box_patterns,
    if_let_guard,
    lazy_cell,
    let_chains,
    min_specialization,
    never_type,
    rustc_private,
    unwrap_infallible
)]

//! This crate contains common type definitions that are used by other crates.

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

use std::sync::OnceLock;

use flux_config as config;
use flux_macros::fluent_messages;
use flux_syntax::surface::{self, NodeId};
use rustc_data_structures::unord::{UnordMap, UnordSet};
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};
use rustc_hash::{FxHashMap, FxHashSet};
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

pub fn theory_funcs() -> &'static [TheoryFunc] {
    static THEORY_FUNCS: OnceLock<Vec<TheoryFunc>> = OnceLock::new();
    THEORY_FUNCS.get_or_init(|| {
        use rty::{
            Sort::{self, *},
            SortCtor::*,
            SortVar,
        };
        vec![
            // Bitvector operations
            TheoryFunc {
                name: Symbol::intern("bv_int_to_bv32"),
                fixpoint_name: Symbol::intern("int_to_bv32"),
                sort: rty::PolyFuncSort::new(
                    0,
                    rty::FuncSort::new(vec![rty::Sort::Int], BitVec(32)),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("bv_bv32_to_int"),
                fixpoint_name: Symbol::intern("bv32_to_int"),
                sort: rty::PolyFuncSort::new(0, rty::FuncSort::new(vec![BitVec(32)], Int)),
            },
            TheoryFunc {
                name: Symbol::intern("bv_sub"),
                fixpoint_name: Symbol::intern("bvsub"),
                sort: rty::PolyFuncSort::new(
                    0,
                    rty::FuncSort::new(vec![BitVec(32), BitVec(32)], BitVec(32)),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("bv_and"),
                fixpoint_name: Symbol::intern("bvand"),
                sort: rty::PolyFuncSort::new(
                    0,
                    rty::FuncSort::new(vec![BitVec(32), BitVec(32)], BitVec(32)),
                ),
            },
            // Set operations
            TheoryFunc {
                name: Symbol::intern("set_empty"),
                fixpoint_name: Symbol::intern("Set_empty"),
                sort: rty::PolyFuncSort::new(
                    1,
                    rty::FuncSort::new(vec![Int], Sort::app(Set, vec![Var(SortVar::from(0))])),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("set_singleton"),
                fixpoint_name: Symbol::intern("Set_sng"),
                sort: rty::PolyFuncSort::new(
                    1,
                    rty::FuncSort::new(
                        vec![Var(SortVar::from(0))],
                        Sort::app(Set, vec![Var(SortVar::from(0))]),
                    ),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("set_union"),
                fixpoint_name: Symbol::intern("Set_cup"),
                sort: rty::PolyFuncSort::new(
                    1,
                    rty::FuncSort::new(
                        vec![
                            Sort::app(Set, vec![Var(SortVar::from(0))]),
                            Sort::app(Set, vec![Var(SortVar::from(0))]),
                        ],
                        Sort::app(Set, vec![Var(SortVar::from(0))]),
                    ),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("set_is_in"),
                fixpoint_name: Symbol::intern("Set_mem"),
                sort: rty::PolyFuncSort::new(
                    1,
                    rty::FuncSort::new(
                        vec![Var(SortVar::from(0)), Sort::app(Set, vec![Var(SortVar::from(0))])],
                        Bool,
                    ),
                ),
            },
            // Map operations
            TheoryFunc {
                name: Symbol::intern("map_default"),
                fixpoint_name: Symbol::intern("Map_default"),
                sort: rty::PolyFuncSort::new(
                    2,
                    rty::FuncSort::new(
                        vec![Var(SortVar::from(1))],
                        Sort::app(Map, vec![Var(SortVar::from(0)), Var(SortVar::from(1))]),
                    ),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("map_select"),
                fixpoint_name: Symbol::intern("Map_select"),
                sort: rty::PolyFuncSort::new(
                    2,
                    rty::FuncSort::new(
                        vec![
                            Sort::app(Map, vec![Var(SortVar::from(0)), Var(SortVar::from(1))]),
                            Var(SortVar::from(0)),
                        ],
                        Var(SortVar::from(1)),
                    ),
                ),
            },
            TheoryFunc {
                name: Symbol::intern("map_store"),
                fixpoint_name: Symbol::intern("Map_store"),
                sort: rty::PolyFuncSort::new(
                    2,
                    rty::FuncSort::new(
                        vec![
                            Sort::app(Map, vec![Var(SortVar::from(0)), Var(SortVar::from(1))]),
                            Var(SortVar::from(0)),
                            Var(SortVar::from(1)),
                        ],
                        Sort::app(Map, vec![Var(SortVar::from(0)), Var(SortVar::from(1))]),
                    ),
                ),
            },
        ]
    })
}

#[derive(Default)]
pub struct Specs {
    pub fn_sigs: UnordMap<OwnerId, surface::FnSpec>,
    pub structs: UnordMap<OwnerId, surface::StructDef>,
    pub traits: UnordMap<OwnerId, surface::Trait>,
    pub impls: UnordMap<OwnerId, surface::Impl>,
    pub enums: UnordMap<OwnerId, surface::EnumDef>,
    pub qualifs: Vec<surface::Qualifier>,
    pub func_defs: Vec<surface::FuncDef>,
    pub sort_decls: Vec<surface::SortDecl>,
    pub ty_aliases: UnordMap<OwnerId, Option<surface::TyAlias>>,
    pub ignores: UnordSet<fhir::IgnoreKey>,
    pub consts: FxHashSet<LocalDefId>,
    pub crate_config: Option<config::CrateConfig>,
    pub extern_specs: FxHashMap<DefId, LocalDefId>,
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
}

pub type ScopeId = NodeId;

#[derive(Default)]
pub struct ResolverOutput {
    pub path_res_map: UnordMap<NodeId, fhir::Res>,
    pub impl_trait_res_map: UnordMap<NodeId, hir::ItemId>,
    // pub func_decls: UnordMap<Symbol, fhir::FuncKind>,
    // pub sort_decls: UnordMap<Symbol, fhir::SortDecl>,
    // pub consts: UnordMap<Symbol, DefId>,
    pub refinements: RefinementResolverOutput,
}

pub struct ResolvedParam {
    pub ident: fhir::Ident,
    pub kind: fhir::ParamKind,
}

#[derive(Clone, Copy)]
pub enum SortRes {
    Int,
    Bool,
    Real,
    User,
    Var(usize),
    Param(DefId),
    /// A `Self` parameter in a trait definition.
    SelfParam {
        trait_id: DefId,
    },
    /// An alias to another sort, e.g., when used inside an impl block
    SelfAlias {
        alias_to: DefId,
    },
}

#[derive(Clone, Copy)]
pub enum FuncRes<Id = fhir::Name> {
    Param(Id),
    Global(fhir::FuncKind),
}

#[derive(Clone, Copy)]
pub struct LocRes<Id = fhir::Name>(pub Id, pub usize);

#[derive(Clone, Copy)]
pub enum PathRes<Id = fhir::Name> {
    Param(Id),
    Const(DefId),
    NumConst(i128),
}

#[derive(Default)]
pub struct RefinementResolverOutput {
    pub param_res_map: UnordMap<NodeId, (fhir::Name, fhir::ParamKind)>,
    pub func_res_map: UnordMap<NodeId, FuncRes>,
    pub loc_res_map: UnordMap<NodeId, LocRes>,
    pub path_res_map: UnordMap<NodeId, PathRes>,
    pub sort_ctor_res_map: UnordMap<NodeId, fhir::SortCtor>,
    pub sort_res_map: UnordMap<NodeId, SortRes>,
    pub implicit_params: UnordMap<NodeId, Vec<(Ident, NodeId)>>,
}
