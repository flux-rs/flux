use rustc_span::def_id::DefId;

use crate::{fhir, rty};

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> Option<rty::PolySig>;
    fn refined_by(&self, def_id: DefId) -> Option<&fhir::RefinedBy>;
    fn adt_def(&self, def_id: DefId) -> Option<&rty::AdtDef>;
    fn variants(&self, def_id: DefId) -> Option<Option<&[rty::PolyVariant]>>;
}

pub type CrateStoreDyn = dyn CrateStore;
