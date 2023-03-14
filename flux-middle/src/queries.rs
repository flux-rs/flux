use std::cell::{OnceCell, RefCell};

use flux_errors::ErrorGuaranteed;
use itertools::Itertools;
use rustc_errors::{FatalError, IntoDiagnostic};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        self,
        refining::{self, Refiner},
    },
    rustc::lowering::{self, UnsupportedDef},
};

type Cache<K, V> = RefCell<FxHashMap<K, V>>;

pub type QueryResult<T = ()> = Result<T, QueryErr>;

#[derive(Debug, Clone)]
pub enum QueryErr {
    UnsupportedType { def_id: DefId, def_span: Span, reason: String },
    Emitted(ErrorGuaranteed),
}

pub struct Providers {
    pub defns: fn(&GlobalEnv) -> QueryResult<rty::Defns>,
    pub qualifiers: fn(&GlobalEnv) -> QueryResult<Vec<rty::Qualifier>>,
    pub check_wf: fn(&GlobalEnv, LocalDefId) -> QueryResult,
    pub adt_def: fn(&GlobalEnv, LocalDefId) -> rty::AdtDef,
    pub type_of: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::Binder<rty::Ty>>,
    pub variants_of: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::PolyVariants>,
    pub fn_sig: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::PolySig>,
    pub generics_of: fn(&GlobalEnv, LocalDefId) -> QueryResult<rty::Generics>,
}

pub struct Queries {
    providers: Providers,
    defns: OnceCell<QueryResult<rty::Defns>>,
    qualifiers: OnceCell<QueryResult<Vec<rty::Qualifier>>>,
    check_wf: Cache<LocalDefId, QueryResult>,
    adt_def: Cache<DefId, rty::AdtDef>,
    generics_of: Cache<DefId, QueryResult<rty::Generics>>,
    predicates_of: Cache<DefId, QueryResult<rty::GenericPredicates>>,
    type_of: Cache<DefId, QueryResult<rty::Binder<rty::Ty>>>,
    variants_of: Cache<DefId, QueryResult<rty::PolyVariants>>,
    fn_sig: Cache<DefId, QueryResult<rty::PolySig>>,
}

impl Queries {
    pub(crate) fn new(providers: Providers) -> Self {
        Self {
            providers,
            defns: OnceCell::new(),
            qualifiers: OnceCell::new(),
            check_wf: Cache::default(),
            adt_def: Cache::default(),
            generics_of: Cache::default(),
            predicates_of: Cache::default(),
            type_of: Cache::default(),
            variants_of: Cache::default(),
            fn_sig: Cache::default(),
        }
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

    pub(crate) fn check_wf(&self, genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult {
        run_with_cache(&self.check_wf, def_id, || (self.providers.check_wf)(genv, def_id))
    }

    pub(crate) fn adt_def(&self, genv: &GlobalEnv, def_id: DefId) -> rty::AdtDef {
        run_with_cache(&self.adt_def, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.adt_def)(genv, local_id)
            } else if let Some(adt_def) = genv.early_cx().cstore.adt_def(def_id) {
                adt_def.clone()
            } else {
                rty::AdtDef::new(genv.tcx.adt_def(def_id), rty::Sort::unit(), vec![], false)
            }
        })
    }

    pub(crate) fn generics_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::Generics> {
        run_with_cache(&self.generics_of, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.generics_of)(genv, local_id)
            } else {
                let generics = lowering::lower_generics(genv.tcx.generics_of(def_id))
                    .map_err(|err| QueryErr::unsupported(genv.tcx, def_id, err))?;
                Ok(refining::refine_generics(&generics))
            }
        })
    }

    pub(crate) fn predicates_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::GenericPredicates> {
        run_with_cache(&self.predicates_of, def_id, || {
            let predicates = genv.tcx.predicates_of(def_id);
            // FIXME(nilehmann) we should propagate this error through the query
            let predicates = lowering::lower_generic_predicates(genv.tcx, genv.sess, predicates)
                .unwrap_or_else(|_| FatalError.raise());

            Refiner::default(genv, &genv.generics_of(def_id)?)
                .refine_generic_predicates(&predicates)
        })
    }

    pub(crate) fn type_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::Binder<rty::Ty>> {
        run_with_cache(&self.type_of, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.type_of)(genv, local_id)
            } else if let Some(ty) = genv.early_cx().cstore.type_of(def_id) {
                Ok(ty.clone())
            } else {
                let rustc_ty = lowering::lower_type_of(genv.tcx, def_id)
                    .map_err(|err| QueryErr::unsupported(genv.tcx, def_id, err))?;
                let ty = genv.refine_default(&genv.generics_of(def_id)?, &rustc_ty)?;
                Ok(rty::Binder::new(ty, rty::Sort::unit()))
            }
        })
    }

    pub(crate) fn variants_of(
        &self,
        genv: &GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::PolyVariants> {
        run_with_cache(&self.variants_of, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.variants_of)(genv, local_id)
            } else if let Some(variants) = genv.early_cx().cstore.variants(def_id) {
                Ok(variants.map(List::from))
            } else {
                let variants = genv
                    .tcx
                    .adt_def(def_id)
                    .variants()
                    .iter()
                    .map(|variant_def| {
                        let variant_def =
                            lowering::lower_variant_def(genv.tcx, def_id, variant_def)
                                .map_err(|err| QueryErr::unsupported(genv.tcx, def_id, err))?;
                        Refiner::default(genv, &genv.generics_of(def_id)?)
                            .refine_variant_def(&variant_def)
                    })
                    .try_collect()?;
                Ok(rty::Opaqueness::Transparent(variants))
            }
        })
    }

    pub(crate) fn fn_sig(&self, genv: &GlobalEnv, def_id: DefId) -> QueryResult<rty::PolySig> {
        run_with_cache(&self.fn_sig, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.fn_sig)(genv, local_id)
            } else if let Some(fn_sig) = genv.early_cx().cstore.fn_sig(def_id) {
                Ok(fn_sig)
            } else {
                let fn_sig = lowering::lower_fn_sig_of(genv.tcx, def_id)
                    .map_err(|err| QueryErr::unsupported(genv.tcx, def_id, err))?
                    .skip_binder();
                Refiner::default(genv, &genv.generics_of(def_id)?).refine_fn_sig(&fn_sig)
            }
        })
    }
}

fn run_with_cache<K, V>(cache: &Cache<K, V>, key: K, f: impl FnOnce() -> V) -> V
where
    K: std::hash::Hash + Eq,
    V: Clone,
{
    cache.borrow_mut().entry(key).or_insert_with(f).clone()
}

impl QueryErr {
    pub fn unsupported(tcx: TyCtxt, def_id: DefId, err: UnsupportedDef) -> Self {
        QueryErr::UnsupportedType { def_id, def_span: tcx.def_span(def_id), reason: err.reason }
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
                builder.note(reason);
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
