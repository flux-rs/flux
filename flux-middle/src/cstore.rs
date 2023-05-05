use rustc_span::def_id::DefId;

use crate::{fhir, rty};

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> Option<rty::EarlyBinder<rty::PolyFnSig>>;
    fn refined_by(&self, def_id: DefId) -> Option<&fhir::RefinedBy>;
    fn adt_def(&self, def_id: DefId) -> Option<&rty::AdtDef>;
    fn variants(
        &self,
        def_id: DefId,
    ) -> Option<rty::Opaqueness<rty::EarlyBinder<&[rty::PolyVariant]>>>;
    fn type_of(&self, def_id: DefId) -> Option<&rty::EarlyBinder<rty::PolyTy>>;
}

pub type CrateStoreDyn = dyn CrateStore;
