use std::{
    cell::{OnceCell, RefCell},
    rc::Rc,
};

use flux_common::iter::IterExt;
use flux_errors::ErrorGuaranteed;
use itertools::Itertools;
use rustc_errors::{FatalError, IntoDiagnostic};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_trait_selection::traits::NormalizeExt;

use crate::{
    fhir::{self, FluxLocalDefId},
    global_env::GlobalEnv,
    intern::List,
    rty::{
        self,
        refining::{self, Refiner},
    },
    rustc::{
        self,
        lowering::{self, UnsupportedReason},
        ty,
    },
};

type Cache<K, V> = RefCell<FxHashMap<K, V>>;

pub type QueryResult<T = ()> = Result<T, QueryErr>;

#[derive(Debug, Clone)]
pub enum QueryErr {
    UnsupportedType { def_id: DefId, def_span: Span, reason: UnsupportedReason },
    Emitted(ErrorGuaranteed),
}

pub struct Providers {
    pub defns: fn(&GlobalEnv) -> QueryResult<rty::Defns>,
    pub qualifiers: fn(&GlobalEnv) -> QueryResult<Vec<rty::Qualifier>>,
    pub check_wf: fn(&GlobalEnv, FluxLocalDefId) -> QueryResult<fhir::WfckResults>,
    pub adt_def: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::AdtDef>,
    pub type_of: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyTy>>,
    pub variants_of: fn(
        &GlobalEnv,
        LocalDefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>,
    pub fn_sig: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>>,
    pub generics_of: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::Generics>,
}

pub struct Queries<'tcx> {
    providers: Providers,
    mir: Cache<LocalDefId, QueryResult<Rc<rustc::mir::Body<'tcx>>>>,
    lower_type_of: Cache<DefId, QueryResult<ty::EarlyBinder<ty::Ty>>>,
    lower_fn_sig: Cache<DefId, QueryResult<ty::EarlyBinder<ty::PolyFnSig>>>,
    defns: OnceCell<QueryResult<rty::Defns>>,
    qualifiers: OnceCell<QueryResult<Vec<rty::Qualifier>>>,
    check_wf: Cache<FluxLocalDefId, QueryResult<Rc<fhir::WfckResults>>>,
    adt_def: Cache<DefId, QueryResult<rty::AdtDef>>,
    generics_of: Cache<DefId, QueryResult<rty::Generics>>,
    predicates_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::GenericPredicates>>>,
    type_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::PolyTy>>>,
    variants_of: Cache<DefId, QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>>,
    fn_sig: Cache<DefId, QueryResult<rty::EarlyBinder<rty::PolyFnSig>>>,
    lower_late_bound_vars: Cache<LocalDefId, QueryResult<List<rustc::ty::BoundVariableKind>>>,
}

impl<'tcx> Queries<'tcx> {
    pub(crate) fn new(providers: Providers) -> Self {
        Self {
            providers,
            mir: Cache::default(),
            lower_type_of: Cache::default(),
            lower_fn_sig: Cache::default(),
            defns: OnceCell::new(),
            qualifiers: OnceCell::new(),
            check_wf: Cache::default(),
            adt_def: Cache::default(),
            generics_of: Cache::default(),
            predicates_of: Cache::default(),
            type_of: Cache::default(),
            variants_of: Cache::default(),
            fn_sig: Cache::default(),
            lower_late_bound_vars: Cache::default(),
        }
    }

    pub(crate) fn mir(
        &self,
        genv: &GlobalEnv<'_, 'tcx>,
        def_id: LocalDefId,
    ) -> QueryResult<Rc<rustc::mir::Body<'tcx>>> {
        run_with_cache(&self.mir, def_id, || {
            let mir = unsafe { flux_common::mir_storage::retrieve_mir_body(genv.tcx, def_id) };
            let mir = rustc::lowering::LoweringCtxt::lower_mir_body(genv.tcx, genv.sess, mir)?;
            Ok(Rc::new(mir))
        })
    }

    pub(crate) fn lower_type_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::EarlyBinder<ty::Ty>> {
        run_with_cache(&self.lower_type_of, def_id, || {
            let ty = genv.tcx.type_of(def_id).subst_identity();
            Ok(ty::EarlyBinder(
                lowering::lower_ty(genv.tcx, ty)
                    .map_err(|reason| QueryErr::unsupported(genv.tcx, def_id, reason))?,
            ))
        })
    }

    pub(crate) fn lower_fn_sig(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        run_with_cache(&self.lower_fn_sig, def_id, || {
            let fn_sig = genv.tcx.fn_sig(def_id);
            let param_env = genv.tcx.param_env(def_id);
            let result = genv
                .tcx
                .infer_ctxt()
                .build()
                .at(&rustc_middle::traits::ObligationCause::dummy(), param_env)
                .normalize(fn_sig.subst_identity());
            Ok(ty::EarlyBinder(
                lowering::lower_fn_sig(genv.tcx, result.value)
                    .map_err(|reason| QueryErr::unsupported(genv.tcx, def_id, reason))?,
            ))
        })
    }

    pub(crate) fn defns(&self, genv: &GlobalEnv) -> QueryResult<&rty::Defns> {
        self.defns
            .get_or_init(|| (self.providers.defns)(genv))
            .as_ref()
            .map_err(Clone::clone)
    }

    pub(crate) fn qualifiers(&self, genv: &GlobalEnv) -> QueryResult<&[rty::Qualifier]> {
        self.qualifiers
            .get_or_init(|| (self.providers.qualifiers)(genv))
            .as_deref()
            .map_err(Clone::clone)
    }

    pub(crate) fn check_wf(
        &self,
        genv: &GlobalEnv,
        flux_id: FluxLocalDefId,
    ) -> QueryResult<Rc<fhir::WfckResults>> {
        run_with_cache(&self.check_wf, flux_id, || {
            let wfckresults = (self.providers.check_wf)(genv, flux_id)?;
            Ok(Rc::new(wfckresults))
        })
    }

    pub(crate) fn adt_def(&self, genv: &GlobalEnv, def_id: DefId) -> QueryResult<rty::AdtDef> {
        run_with_cache(&self.adt_def, def_id, || {
            let def_id = *genv.lookup_extern(&def_id).unwrap_or(&def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.adt_def)(genv, local_id)
            } else if let Some(adt_def) = genv.early_cx().cstore.adt_def(def_id) {
                Ok(adt_def.clone())
            } else {
                Ok(rty::AdtDef::new(genv.tcx.adt_def(def_id), rty::Sort::unit(), vec![], false))
            }
        })
    }

    pub(crate) fn generics_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::Generics> {
        run_with_cache(&self.generics_of, def_id, || {
            let def_id = *genv.lookup_extern(&def_id).unwrap_or(&def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.generics_of)(genv, local_id)
            } else {
                let generics = lowering::lower_generics(genv.tcx.generics_of(def_id))
                    .map_err(|reason| QueryErr::unsupported(genv.tcx, def_id, reason))?;
                Ok(refining::refine_generics(&generics))
            }
        })
    }

    pub(crate) fn predicates_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        run_with_cache(&self.predicates_of, def_id, || {
            let predicates = genv.tcx.predicates_of(def_id);
            // FIXME(nilehmann) we should propagate this error through the query
            let predicates = lowering::lower_generic_predicates(genv.tcx, genv.sess, predicates)
                .unwrap_or_else(|_| FatalError.raise());

            let predicates = Refiner::default(genv, &genv.generics_of(def_id)?)
                .refine_generic_predicates(&predicates)?;
            Ok(rty::EarlyBinder(predicates))
        })
    }

    pub(crate) fn type_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::PolyTy>> {
        run_with_cache(&self.type_of, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.type_of)(genv, local_id)
            } else if let Some(ty) = genv.early_cx().cstore.type_of(def_id) {
                Ok(ty.clone())
            } else {
                let rustc_ty = genv.lower_type_of(def_id)?.skip_binder();
                let ty = genv.refine_default(&genv.generics_of(def_id)?, &rustc_ty)?;
                Ok(rty::EarlyBinder(rty::Binder::with_sort(ty, rty::Sort::unit())))
            }
        })
    }

    pub(crate) fn variants_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        run_with_cache(&self.variants_of, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.variants_of)(genv, local_id)
            } else if let Some(variants) = genv.early_cx().cstore.variants(def_id) {
                Ok(variants.map(|variants| variants.map(List::from)))
            } else {
                let variants = genv
                    .tcx
                    .adt_def(def_id)
                    .variants()
                    .iter()
                    .map(|variant_def| {
                        let fields = variant_def
                            .fields
                            .iter()
                            .map(|field| Ok(genv.lower_type_of(field.did)?.skip_binder()))
                            .try_collect_vec::<_, QueryErr>()?;
                        let ret = genv.lower_type_of(def_id)?.skip_binder();
                        Refiner::default(genv, &genv.generics_of(def_id)?)
                            .refine_variant_def(&fields, &ret)
                    })
                    .try_collect()?;
                Ok(rty::Opaqueness::Transparent(rty::EarlyBinder(variants)))
            }
        })
    }

    pub(crate) fn fn_sig(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        run_with_cache(&self.fn_sig, def_id, || {
            // If it's an extern_fn, resolve it to its local fn_sig's def_id,
            // otherwise don't change it.
            let def_id = *genv.lookup_extern(&def_id).unwrap_or(&def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.fn_sig)(genv, local_id)
            } else if let Some(fn_sig) = genv.early_cx().cstore.fn_sig(def_id) {
                Ok(fn_sig)
            } else {
                let fn_sig = genv.lower_fn_sig(def_id)?.skip_binder();
                let fn_sig = Refiner::default(genv, &genv.generics_of(def_id)?)
                    .refine_poly_fn_sig(&fn_sig)?;
                Ok(rty::EarlyBinder(fn_sig))
            }
        })
    }

    pub(crate) fn lower_late_bound_vars(
        &self,
        genv: &GlobalEnv,
        def_id: LocalDefId,
    ) -> QueryResult<List<rustc::ty::BoundVariableKind>> {
        run_with_cache(&self.lower_late_bound_vars, def_id, || {
            let hir_id = genv.hir().local_def_id_to_hir_id(def_id);
            let bound_vars = genv.tcx.late_bound_vars(hir_id);
            lowering::lower_bound_vars(bound_vars)
                .map_err(|reason| QueryErr::unsupported(genv.tcx, def_id.to_def_id(), reason))
        })
    }
}

fn run_with_cache<K, V>(cache: &Cache<K, V>, key: K, f: impl FnOnce() -> V) -> V
where
    K: std::hash::Hash + Eq,
    V: Clone,
{
    if let Some(v) = cache.borrow().get(&key) {
        return v.clone();
    }
    let v = f();
    cache.borrow_mut().insert(key, v.clone());
    v
}

impl QueryErr {
    pub fn unsupported(tcx: TyCtxt, def_id: DefId, reason: UnsupportedReason) -> Self {
        QueryErr::UnsupportedType { def_id, def_span: tcx.def_span(def_id), reason }
    }
}

impl<'a> IntoDiagnostic<'a> for QueryErr {
    fn into_diagnostic(
        self,
        handler: &'a rustc_errors::Handler,
    ) -> rustc_errors::DiagnosticBuilder<'a, ErrorGuaranteed> {
        use crate::fluent_generated as fluent;
        match self {
            QueryErr::UnsupportedType { reason, .. } => {
                let mut builder = handler.struct_err_with_code(
                    fluent::middle_query_unsupported_type,
                    flux_errors::diagnostic_id(),
                );
                builder.note(reason.descr);
                builder
            }
            QueryErr::Emitted(_) => {
                let mut builder = handler.struct_err("QueryErr::Emitted should be emitted");
                builder.downgrade_to_delayed_bug();
                builder
            }
        }
    }
}

impl From<ErrorGuaranteed> for QueryErr {
    fn from(err: ErrorGuaranteed) -> Self {
        Self::Emitted(err)
    }
}
