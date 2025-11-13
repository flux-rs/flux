use std::rc::Rc;

use rustc_hir::def_id::CrateNum;
use rustc_span::def_id::DefId;

use crate::{def_id::FluxDefId, queries::QueryResult, rty};

pub type OptResult<T> = Option<QueryResult<T>>;

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::PolyFnSig>>;
    fn adt_def(&self, def_id: DefId) -> OptResult<rty::AdtDef>;
    fn adt_sort_def(&self, def_id: DefId) -> OptResult<rty::AdtSortDef>;
    fn generics_of(&self, def_id: DefId) -> OptResult<rty::Generics>;
    fn refinement_generics_of(
        &self,
        def_id: DefId,
    ) -> OptResult<rty::EarlyBinder<rty::RefinementGenerics>>;
    fn item_bounds(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::Clauses>>;
    fn predicates_of(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::GenericPredicates>>;
    fn assoc_refinements_of(&self, def_id: DefId) -> OptResult<rty::AssocRefinements>;
    fn constant_info(&self, def_id: DefId) -> OptResult<rty::ConstantInfo>;
    fn assoc_refinements_def(&self, key: FluxDefId) -> OptResult<rty::EarlyBinder<rty::Lambda>>;
    fn default_assoc_refinements_def(
        &self,
        key: FluxDefId,
    ) -> OptResult<Option<rty::EarlyBinder<rty::Lambda>>>;
    fn sort_of_assoc_reft(&self, key: FluxDefId) -> OptResult<rty::EarlyBinder<rty::FuncSort>>;
    fn variants_of(
        &self,
        def_id: DefId,
    ) -> OptResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>;
    fn type_of(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::TyOrCtor>>;
    fn normalized_defns(&self, krate: CrateNum) -> Rc<rty::NormalizedDefns>;
    fn func_sort(&self, def_id: FluxDefId) -> Option<rty::PolyFuncSort>;
    fn func_span(&self, def_id: FluxDefId) -> Option<rustc_span::Span>;
    fn sort_decl_param_count(&self, def_id: FluxDefId) -> Option<usize>;
    fn no_panic(&self, def_id: DefId) -> Option<bool>;
}

pub type CrateStoreDyn = dyn CrateStore;
