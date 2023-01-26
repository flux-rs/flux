use rustc_span::{def_id::DefId, Symbol};

use crate::rty;

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> Option<rty::PolySig>;
    fn index_sorts(&self, def_id: DefId) -> Option<&[rty::Sort]>;
    fn field_index(&self, def_id: DefId, fld: Symbol) -> Option<usize>;
    fn field_sort(&self, def_id: DefId, fld: Symbol) -> Option<&rty::Sort>;
    fn adt_def(&self, def_id: DefId) -> Option<&rty::AdtDef>;
    fn variants(&self, def_id: DefId) -> Option<Option<&[rty::PolyVariant]>>;
}

pub type CrateStoreDyn = dyn CrateStore;
