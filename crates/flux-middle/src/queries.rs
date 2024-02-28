use std::{
    cell::{OnceCell, RefCell},
    rc::Rc,
};

use flux_common::iter::IterExt;
use flux_errors::ErrorGuaranteed;
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};
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
        lowering::{self, UnsupportedErr, UnsupportedReason},
        ty,
    },
};

type Cache<K, V> = RefCell<UnordMap<K, V>>;

pub type QueryResult<T = ()> = Result<T, QueryErr>;

#[derive(Debug, Clone)]
pub enum QueryErr {
    Unsupported { def_id: DefId, def_span: Span, err: UnsupportedErr },
    InvalidGenericArg { def_id: DefId, def_span: Span },
    Emitted(ErrorGuaranteed),
}

pub struct Providers {
    pub collect_specs: fn(GlobalEnv) -> crate::Specs,
    pub resolve_crate: fn(GlobalEnv) -> crate::ResolverOutput,
    pub fhir_crate: for<'genv> fn(GlobalEnv<'genv, '_>) -> fhir::Crate<'genv>,
    pub qualifiers: fn(GlobalEnv) -> QueryResult<Vec<rty::Qualifier>>,
    pub spec_func_defns: fn(GlobalEnv) -> QueryResult<rty::SpecFuncDefns>,
    pub spec_func_decls: fn(GlobalEnv) -> FxHashMap<Symbol, rty::SpecFuncDecl>,
    pub adt_sort_def_of: fn(GlobalEnv, LocalDefId) -> rty::AdtSortDef,
    pub check_wf: for<'genv> fn(
        GlobalEnv<'genv, '_>,
        FluxLocalDefId,
    ) -> QueryResult<Rc<rty::WfckResults<'genv>>>,
    pub adt_def: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::AdtDef>,
    pub type_of: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::EarlyBinder<rty::TyCtor>>,
    pub variants_of: fn(
        GlobalEnv,
        LocalDefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>,
    pub fn_sig: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>>,
    pub generics_of: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::Generics>,
    pub refinement_generics_of: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::RefinementGenerics>,
    pub predicates_of:
        fn(GlobalEnv, LocalDefId) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>>,
    pub assoc_refinements_of: fn(GlobalEnv, LocalDefId) -> rty::AssocRefinements,
    pub sort_of_assoc_reft:
        fn(GlobalEnv, LocalDefId, Symbol) -> Option<rty::EarlyBinder<rty::FuncSort>>,
    pub assoc_refinement_def:
        fn(GlobalEnv, LocalDefId, Symbol) -> QueryResult<rty::EarlyBinder<rty::Lambda>>,
    pub item_bounds: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>>,
}

macro_rules! empty_query {
    () => {
        flux_common::bug!("query not provided")
    };
}

impl Default for Providers {
    fn default() -> Self {
        Self {
            collect_specs: |_| empty_query!(),
            fhir_crate: |_| empty_query!(),
            resolve_crate: |_| empty_query!(),
            spec_func_defns: |_| empty_query!(),
            spec_func_decls: |_| empty_query!(),
            qualifiers: |_| empty_query!(),
            adt_sort_def_of: |_, _| empty_query!(),
            check_wf: |_, _| empty_query!(),
            adt_def: |_, _| empty_query!(),
            type_of: |_, _| empty_query!(),
            variants_of: |_, _| empty_query!(),
            fn_sig: |_, _| empty_query!(),
            generics_of: |_, _| empty_query!(),
            refinement_generics_of: |_, _| empty_query!(),
            predicates_of: |_, _| empty_query!(),
            assoc_refinements_of: |_, _| empty_query!(),
            assoc_refinement_def: |_, _, _| empty_query!(),
            sort_of_assoc_reft: |_, _, _| empty_query!(),
            item_bounds: |_, _| empty_query!(),
        }
    }
}

pub struct Queries<'genv, 'tcx> {
    pub(crate) providers: Providers,
    mir: Cache<LocalDefId, QueryResult<Rc<rustc::mir::Body<'tcx>>>>,
    collect_specs: OnceCell<crate::Specs>,
    resolve_crate: OnceCell<crate::ResolverOutput>,
    fhir_crate: OnceCell<fhir::Crate<'genv>>,
    lower_generics_of: Cache<DefId, QueryResult<ty::Generics<'tcx>>>,
    lower_predicates_of: Cache<DefId, QueryResult<ty::GenericPredicates>>,
    lower_type_of: Cache<DefId, QueryResult<ty::EarlyBinder<ty::Ty>>>,
    lower_fn_sig: Cache<DefId, QueryResult<ty::EarlyBinder<ty::PolyFnSig>>>,
    defns: OnceCell<QueryResult<rty::SpecFuncDefns>>,
    func_decls: OnceCell<FxHashMap<Symbol, rty::SpecFuncDecl>>,
    qualifiers: OnceCell<QueryResult<Vec<rty::Qualifier>>>,
    adt_sort_def_of: Cache<DefId, rty::AdtSortDef>,
    check_wf: Cache<FluxLocalDefId, QueryResult<Rc<rty::WfckResults<'genv>>>>,
    adt_def: Cache<DefId, QueryResult<rty::AdtDef>>,
    generics_of: Cache<DefId, QueryResult<rty::Generics>>,
    refinement_generics_of: Cache<DefId, QueryResult<rty::RefinementGenerics>>,
    predicates_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::GenericPredicates>>>,
    assoc_refinements_of: Cache<DefId, rty::AssocRefinements>,
    assoc_refinement_def: Cache<(DefId, Symbol), QueryResult<rty::EarlyBinder<rty::Lambda>>>,
    sort_of_assoc_reft: Cache<(DefId, Symbol), Option<rty::EarlyBinder<rty::FuncSort>>>,
    item_bounds: Cache<DefId, QueryResult<rty::EarlyBinder<List<rty::Clause>>>>,
    type_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::TyCtor>>>,
    variants_of: Cache<DefId, QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>>,
    fn_sig: Cache<DefId, QueryResult<rty::EarlyBinder<rty::PolyFnSig>>>,
    lower_late_bound_vars: Cache<LocalDefId, QueryResult<List<rustc::ty::BoundVariableKind>>>,
}

impl<'genv, 'tcx> Queries<'genv, 'tcx> {
    pub(crate) fn new(providers: Providers) -> Self {
        Self {
            providers,
            mir: Default::default(),
            collect_specs: Default::default(),
            fhir_crate: Default::default(),
            resolve_crate: Default::default(),
            lower_generics_of: Default::default(),
            lower_predicates_of: Default::default(),
            lower_type_of: Default::default(),
            lower_fn_sig: Default::default(),
            defns: Default::default(),
            func_decls: Default::default(),
            qualifiers: Default::default(),
            adt_sort_def_of: Default::default(),
            check_wf: Default::default(),
            adt_def: Default::default(),
            generics_of: Default::default(),
            refinement_generics_of: Default::default(),
            predicates_of: Default::default(),
            assoc_refinements_of: Default::default(),
            assoc_refinement_def: Default::default(),
            sort_of_assoc_reft: Default::default(),
            item_bounds: Default::default(),
            type_of: Default::default(),
            variants_of: Default::default(),
            fn_sig: Default::default(),
            lower_late_bound_vars: Default::default(),
        }
    }

    pub(crate) fn mir(
        &self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
    ) -> QueryResult<Rc<rustc::mir::Body<'tcx>>> {
        run_with_cache(&self.mir, def_id, || {
            let mir = unsafe { flux_common::mir_storage::retrieve_mir_body(genv.tcx(), def_id) };
            let mir = rustc::lowering::LoweringCtxt::lower_mir_body(genv.tcx(), genv.sess(), mir)?;
            Ok(Rc::new(mir))
        })
    }

    pub(crate) fn collect_specs(&'genv self, genv: GlobalEnv<'genv, 'tcx>) -> &'genv crate::Specs {
        self.collect_specs
            .get_or_init(|| (self.providers.collect_specs)(genv))
    }

    pub(crate) fn resolve_crate(
        &'genv self,
        genv: GlobalEnv<'genv, 'tcx>,
    ) -> &'genv crate::ResolverOutput {
        self.resolve_crate
            .get_or_init(|| (self.providers.resolve_crate)(genv))
    }

    pub(crate) fn fhir_crate(
        &'genv self,
        genv: GlobalEnv<'genv, 'tcx>,
    ) -> &'genv fhir::Crate<'genv> {
        self.fhir_crate
            .get_or_init(|| (self.providers.fhir_crate)(genv))
    }

    pub(crate) fn lower_generics_of(
        &self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: DefId,
    ) -> QueryResult<ty::Generics<'tcx>> {
        run_with_cache(&self.lower_generics_of, def_id, || {
            let generics = genv.tcx().generics_of(def_id);
            lowering::lower_generics(generics)
                .map_err(UnsupportedReason::into_err)
                .map_err(|err| QueryErr::unsupported(genv.tcx(), def_id, err))
        })
    }

    pub(crate) fn lower_predicates_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::GenericPredicates> {
        run_with_cache(&self.lower_predicates_of, def_id, || {
            let predicates = genv.tcx().predicates_of(def_id);
            lowering::lower_generic_predicates(genv.tcx(), predicates)
                .map_err(|err| QueryErr::unsupported(genv.tcx(), def_id, err))
        })
    }

    pub(crate) fn lower_type_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::EarlyBinder<ty::Ty>> {
        run_with_cache(&self.lower_type_of, def_id, || {
            let ty = genv.tcx().type_of(def_id).instantiate_identity();
            Ok(ty::EarlyBinder(
                lowering::lower_ty(genv.tcx(), ty)
                    .map_err(UnsupportedReason::into_err)
                    .map_err(|err| QueryErr::unsupported(genv.tcx(), def_id, err))?,
            ))
        })
    }

    pub(crate) fn lower_fn_sig(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        run_with_cache(&self.lower_fn_sig, def_id, || {
            let fn_sig = genv.tcx().fn_sig(def_id);
            let param_env = genv.tcx().param_env(def_id);
            let result = genv
                .tcx()
                .infer_ctxt()
                .build()
                .at(&rustc_middle::traits::ObligationCause::dummy(), param_env)
                .normalize(fn_sig.instantiate_identity());
            Ok(ty::EarlyBinder(
                lowering::lower_fn_sig(genv.tcx(), result.value)
                    .map_err(UnsupportedReason::into_err)
                    .map_err(|err| QueryErr::unsupported(genv.tcx(), def_id, err))?,
            ))
        })
    }

    pub(crate) fn spec_func_defns(&self, genv: GlobalEnv) -> QueryResult<&rty::SpecFuncDefns> {
        self.defns
            .get_or_init(|| (self.providers.spec_func_defns)(genv))
            .as_ref()
            .map_err(Clone::clone)
    }

    pub(crate) fn func_decls(&self, genv: GlobalEnv) -> &FxHashMap<Symbol, rty::SpecFuncDecl> {
        self.func_decls
            .get_or_init(|| (self.providers.spec_func_decls)(genv))
    }

    pub(crate) fn qualifiers(&self, genv: GlobalEnv) -> QueryResult<&[rty::Qualifier]> {
        self.qualifiers
            .get_or_init(|| (self.providers.qualifiers)(genv))
            .as_deref()
            .map_err(Clone::clone)
    }

    pub(crate) fn adt_sort_def_of(&self, genv: GlobalEnv, def_id: DefId) -> rty::AdtSortDef {
        run_with_cache(&self.adt_sort_def_of, def_id, || {
            let extern_id = genv.lookup_extern(def_id);
            let def_id = extern_id.unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.adt_sort_def_of)(genv, local_id)
            } else if let Some(adt_def) = genv.cstore().adt_def(def_id) {
                adt_def.sort_def().clone()
            } else {
                rty::AdtSortDef::new(def_id, vec![], vec![])
            }
        })
    }

    pub(crate) fn check_wf(
        &self,
        genv: GlobalEnv<'genv, '_>,
        flux_id: FluxLocalDefId,
    ) -> QueryResult<Rc<rty::WfckResults<'genv>>> {
        run_with_cache(&self.check_wf, flux_id, || (self.providers.check_wf)(genv, flux_id))
    }

    pub(crate) fn adt_def(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<rty::AdtDef> {
        run_with_cache(&self.adt_def, def_id, || {
            let extern_id = genv.lookup_extern(def_id);
            let def_id = extern_id.unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.adt_def)(genv, local_id)
            } else if let Some(adt_def) = genv.cstore().adt_def(def_id) {
                Ok(adt_def.clone())
            } else {
                let adt_def = if let Some(extern_id) = extern_id {
                    lowering::lower_adt_def(&genv.tcx().adt_def(extern_id))
                } else {
                    lowering::lower_adt_def(&genv.tcx().adt_def(def_id))
                };
                Ok(rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id), vec![], false))
            }
        })
    }

    pub(crate) fn generics_of(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<rty::Generics> {
        run_with_cache(&self.generics_of, def_id, || {
            let def_id = genv.lookup_extern(def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.generics_of)(genv, local_id)
            } else {
                let generics = genv.lower_generics_of(def_id)?;
                refining::refine_generics(&generics)
            }
        })
    }

    pub(crate) fn refinement_generics_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::RefinementGenerics> {
        run_with_cache(&self.refinement_generics_of, def_id, || {
            let def_id = genv.lookup_extern(def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.refinement_generics_of)(genv, local_id)
            } else {
                let parent = genv.tcx().generics_of(def_id).parent;
                Ok(rty::RefinementGenerics { parent, parent_count: 0, params: List::empty() })
            }
        })
    }

    pub(crate) fn item_bounds(
        &self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
        run_with_cache(&self.item_bounds, def_id, || {
            let def_id = genv.lookup_extern(def_id).unwrap_or(def_id);

            if let Some(local_id) = def_id.as_local() {
                (self.providers.item_bounds)(genv, local_id)
            } else {
                let bounds = genv.tcx().item_bounds(def_id).skip_binder();
                let clauses = lowering::lower_item_bounds(genv.tcx(), bounds)
                    .map_err(|err| QueryErr::unsupported(genv.tcx(), def_id, err))?;

                let clauses =
                    Refiner::default(genv, &genv.generics_of(def_id)?).refine_clauses(&clauses)?;

                Ok(rty::EarlyBinder(clauses))
            }
        })
    }

    pub(crate) fn predicates_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        run_with_cache(&self.predicates_of, def_id, || {
            let def_id = genv.lookup_extern(def_id).unwrap_or(def_id);

            if let Some(local_id) = def_id.as_local() {
                (self.providers.predicates_of)(genv, local_id)
            } else {
                let predicates = genv.lower_predicates_of(def_id)?;
                let predicates = Refiner::default(genv, &genv.generics_of(def_id)?)
                    .refine_generic_predicates(&predicates)?;
                Ok(rty::EarlyBinder(predicates))
            }
        })
    }

    pub(crate) fn assoc_refinements_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> rty::AssocRefinements {
        run_with_cache(&self.assoc_refinements_of, def_id, || {
            let def_id = genv.lookup_extern(def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.assoc_refinements_of)(genv, local_id)
            } else {
                rty::AssocRefinements::default()
            }
        })
    }

    pub(crate) fn assoc_refinement_def(
        &self,
        genv: GlobalEnv,
        impl_id: DefId,
        name: Symbol,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        run_with_cache(&self.assoc_refinement_def, (impl_id, name), || {
            let impl_id = genv.lookup_extern(impl_id).unwrap_or(impl_id);
            if let Some(local_id) = impl_id.as_local() {
                (self.providers.assoc_refinement_def)(genv, local_id, name)
            } else {
                todo!("implement for external crates")
            }
        })
    }

    pub(crate) fn sort_of_assoc_reft(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
        name: Symbol,
    ) -> Option<rty::EarlyBinder<rty::FuncSort>> {
        run_with_cache(&self.sort_of_assoc_reft, (def_id, name), || {
            let impl_id = genv.lookup_extern(def_id).unwrap_or(def_id);
            if let Some(local_id) = impl_id.as_local() {
                (self.providers.sort_of_assoc_reft)(genv, local_id, name)
            } else {
                todo!("implement for external crates")
            }
        })
    }

    pub(crate) fn type_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::TyCtor>> {
        run_with_cache(&self.type_of, def_id, || {
            if let Some(local_id) = def_id.as_local() {
                (self.providers.type_of)(genv, local_id)
            } else if let Some(ty) = genv.cstore().type_of(def_id) {
                Ok(ty.clone())
            } else {
                // If we're given a type parameter, provide the generics of the parent container.
                let generics_def_id = match genv.def_kind(def_id) {
                    DefKind::TyParam => genv.tcx().parent(def_id),
                    _ => def_id,
                };
                let generics = genv.generics_of(generics_def_id)?;
                let ty = genv.lower_type_of(def_id)?.skip_binder();
                let ty = Refiner::default(genv, &generics).refine_ty(&ty)?;
                Ok(rty::EarlyBinder(rty::Binder::with_sort(ty, rty::Sort::unit())))
            }
        })
    }

    pub(crate) fn variants_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        run_with_cache(&self.variants_of, def_id, || {
            let (def_id, _is_extern) = match genv.lookup_extern(def_id) {
                Some(def_id) => (def_id, true),
                None => (def_id, false),
            };
            if let Some(local_id) = def_id.as_local() {
                (self.providers.variants_of)(genv, local_id)
            } else if let Some(variants) = genv.cstore().variants(def_id) {
                Ok(variants.map(|variants| variants.map(List::from)))
            } else {
                let variants = genv
                    .tcx()
                    .adt_def(def_id)
                    .variants()
                    .iter()
                    .map(|variant_def| {
                        let fields = variant_def
                            .fields
                            .iter()
                            .map(|field| Ok(genv.lower_type_of(field.did)?.skip_binder()))
                            .try_collect_vec::<_, QueryErr>()?;
                        Refiner::default(genv, &genv.generics_of(def_id)?)
                            .refine_variant_def(def_id, &fields)
                    })
                    .try_collect()?;
                Ok(rty::Opaqueness::Transparent(rty::EarlyBinder(variants)))
            }
        })
    }

    pub(crate) fn fn_sig(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        run_with_cache(&self.fn_sig, def_id, || {
            // If it's an extern_fn, resolve it to its local fn_sig's def_id,
            // otherwise don't change it.
            let def_id = genv.lookup_extern(def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.fn_sig)(genv, local_id)
            } else if let Some(fn_sig) = genv.cstore().fn_sig(def_id) {
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
        genv: GlobalEnv,
        def_id: LocalDefId,
    ) -> QueryResult<List<rustc::ty::BoundVariableKind>> {
        run_with_cache(&self.lower_late_bound_vars, def_id, || {
            let hir_id = genv.hir().local_def_id_to_hir_id(def_id);
            let bound_vars = genv.tcx().late_bound_vars(hir_id);
            lowering::lower_bound_vars(bound_vars)
                .map_err(UnsupportedReason::into_err)
                .map_err(|err| QueryErr::unsupported(genv.tcx(), def_id.to_def_id(), err))
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
    pub fn unsupported(tcx: TyCtxt, def_id: DefId, err: UnsupportedErr) -> Self {
        QueryErr::Unsupported { def_id, def_span: tcx.def_span(def_id), err }
    }
}

impl<'a> IntoDiagnostic<'a> for QueryErr {
    fn into_diagnostic(
        self,
        handler: &'a rustc_errors::Handler,
    ) -> rustc_errors::DiagnosticBuilder<'a, ErrorGuaranteed> {
        use crate::fluent_generated as fluent;
        match self {
            QueryErr::Unsupported { err, def_span, .. } => {
                let span = err.span.unwrap_or(def_span);
                let mut builder = handler.struct_span_err_with_code(
                    span,
                    fluent::middle_query_unsupported,
                    flux_errors::diagnostic_id(),
                );
                builder.note(err.descr);
                builder
            }
            QueryErr::Emitted(_) => {
                let mut builder = handler.struct_err("QueryErr::Emitted should be emitted");
                builder.downgrade_to_delayed_bug();
                builder
            }
            QueryErr::InvalidGenericArg { def_span, .. } => {
                let builder = handler.struct_span_err_with_code(
                    def_span,
                    fluent::middle_query_invalid_generic_arg,
                    flux_errors::diagnostic_id(),
                );
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
