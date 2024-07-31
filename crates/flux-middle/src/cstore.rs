use rustc_span::{def_id::DefId, Symbol};

use crate::{intern::List, queries::QueryResult, rty};

pub type OptResult<T> = Option<QueryResult<T>>;

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::PolyFnSig>>;
    fn adt_def(&self, def_id: DefId) -> OptResult<rty::AdtDef>;
    fn adt_sort_def(&self, def_id: DefId) -> OptResult<rty::AdtSortDef>;
    fn generics_of(&self, def_id: DefId) -> OptResult<rty::Generics>;
    fn refinement_generics_of(&self, def_id: DefId) -> OptResult<rty::RefinementGenerics>;
    fn item_bounds(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<List<rty::Clause>>>;
    fn predicates_of(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::GenericPredicates>>;
    fn assoc_refinements_of(&self, def_id: DefId) -> OptResult<rty::AssocRefinements>;
    fn assoc_refinements_def(
        &self,
        def_id: DefId,
        name: Symbol,
    ) -> OptResult<rty::EarlyBinder<rty::Lambda>>;
    fn sort_of_assoc_reft(
        &self,
        def_id: DefId,
        name: Symbol,
    ) -> OptResult<Option<rty::EarlyBinder<rty::FuncSort>>>;
    fn variants(
        &self,
        def_id: DefId,
    ) -> OptResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>;
    fn type_of(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::TyCtor>>;
}

pub type CrateStoreDyn = dyn CrateStore;
