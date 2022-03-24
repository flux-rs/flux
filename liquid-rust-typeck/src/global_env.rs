use std::cell::RefCell;

use liquid_rust_common::errors::ErrorReported;
use liquid_rust_core::resolve::Resolver;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ty::{self, BaseTy, Sort};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
    pub adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
        adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    ) -> Self {
        GlobalEnv { fn_specs, adt_defs, tcx }
    }

    fn lookup_default_spec(
        &self,
        local_def: LocalDefId,
        span: Span,
    ) -> Result<ty::FnSpec, ErrorReported> {
        let mut resolver = Resolver::from_fn(self.tcx, local_def)?;
        let fn_sig = resolver.default_sig(local_def, span)?;
        // TODO -- wf needs a bunch of stuff not in scope here.
        // of course "default" sigs SHOULD be well-formed so perhaps redundant
        // wf.check_fn_sig(&fn_sig)?;
        let fn_sig = crate::lowering::LoweringCtxt::lower_fn_sig(fn_sig);
        Ok(ty::FnSpec { fn_sig, assume: true })
    }

    pub fn lookup_fn_sig(&self, did: DefId, span: Span) -> ty::Binders<ty::FnSig> {
        let local_def = did.as_local().unwrap();
        if let Some(fn_spec) = self.fn_specs.borrow().get(&local_def) {
            return fn_spec.fn_sig.clone();
        }
        match self.lookup_default_spec(local_def, span) {
            Ok(fn_spec) => {
                let mut tmp = self.fn_specs.borrow_mut();
                tmp.insert(local_def, fn_spec.clone());
                return fn_spec.fn_sig;
            }
            Err(e) => {
                panic!("Oh no! lookup_fn_sig {:?}", e)
            }
        }
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
