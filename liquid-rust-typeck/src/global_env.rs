use std::cell::RefCell;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
use rustc_span::Span;

use crate::ty::{self, BaseTy, Sort, DefTy};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
    pub adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

fn default_ty(_t: rustc_middle::ty::Ty) -> DefTy {
    panic!("TODO")
}

fn default_defn_sig(rust_sig: rustc_middle::ty::FnSig, span: Span) -> ty::DefFnSig {
    let mut requires = Vec::new();
    let in_tys = rust_sig.inputs();
    let out_ty = rust_sig.output();
    let returns = default_ty(rust_sig.output());
    let ensures = vec![];
    let wherep = None;
    ty::surface::FnSig { requires, returns, ensures, wherep, span }
}

fn desugar_defn_sig(defn_sig: ty::DefFnSig) -> ty::FnSig {
   panic!("todo")
}

fn default_fn_spec(rust_sig: rustc_middle::ty::FnSig, span: Span) -> ty::FnSpec {
    let params = vec![];
    let defn_sig = default_defn_sig(rust_sig, span);
    let value = desugar_defn_sig(defn_sig);
    let fn_sig = ty::Binders { params, value };
    let assume = true;
    ty::FnSpec { fn_sig, assume }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
        adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    ) -> Self {
        GlobalEnv { fn_specs, adt_defs, tcx }
    }


    pub fn lookup_fn_sig(&self, did: DefId, span: Span) -> ty::Binders<ty::FnSig> {
        // RJ:TODO -- make it cry when function is missing, THEN populate function from rust-sig.
        // Missing -- due to EXTERNAL crate OR because its LOCAL but had no annotations.
        // do this: https://ucsd-progsys.slack.com/archives/DU17X62Q5/p1647450667607229
        // see resolve Result<Resolver<'tcx>, ErrorReported> for error handling
        let local_def = did.as_local().unwrap();
        if let Some(fn_spec) = self.fn_specs.borrow().get(&local_def) {
            let z = fn_spec.fn_sig.clone();
            return z;
        // &self.fn_specs[&local_def].fn_sig
        }
        if let Some(rust_sig) = self.tcx.fn_sig(did).no_bound_vars() {
            let fn_spec = default_fn_spec(rust_sig, span);
            print!("Using default spec for function {:?} : {:?}", did, fn_spec);
            self.fn_specs.borrow_mut().insert(local_def, fn_spec.clone());
            return fn_spec.fn_sig
        }
        panic!("Oh no! lookup_fn_sig {:?}", did)
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
