use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;

use crate::ty::{self, BaseTy, Sort};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: FxHashMap<LocalDefId, ty::FnSpec>,
    pub adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: FxHashMap<LocalDefId, ty::FnSpec>,
        adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    ) -> Self {
        GlobalEnv { fn_specs, adt_defs, tcx }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &ty::Binders<ty::FnSig> {
        // RJ:TODO -- make it cry when function is missing, THEN populate function from rust-sig.
        // Missing -- due to EXTERNAL crate OR because its LOCAL but had no annotations.
        // do this: https://ucsd-progsys.slack.com/archives/DU17X62Q5/p1647450667607229
        // see resolve Result<Resolver<'tcx>, ErrorReported> for error handling
        &self.fn_specs[&did.as_local().unwrap()].fn_sig
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, did: DefId) -> &ty::AdtDef {
        &self.adt_defs[&did.as_local().unwrap()]
    }

    pub fn sorts(&self, bty: &BaseTy) -> Vec<Sort> {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => vec![Sort::int()],
            BaseTy::Bool => vec![Sort::bool()],
            BaseTy::Adt(def_id, _) => {
                if let Some(adt_def) = def_id.as_local().and_then(|did| self.adt_defs.get(&did)) {
                    adt_def.sorts()
                } else {
                    vec![]
                }
            }
        }
    }
}
