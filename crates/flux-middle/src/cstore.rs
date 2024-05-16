use rustc_span::def_id::DefId;

use crate::{queries::QueryResult, rty};

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> Option<QueryResult<rty::EarlyBinder<rty::PolyFnSig>>>;
    fn adt_def(&self, def_id: DefId) -> Option<QueryResult<rty::AdtDef>>;
    fn variants(
        &self,
        def_id: DefId,
    ) -> Option<QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>>;
    fn type_of(&self, def_id: DefId) -> Option<QueryResult<rty::EarlyBinder<rty::TyCtor>>>;
}

pub type CrateStoreDyn = dyn CrateStore;
