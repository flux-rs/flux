use std::{
    cell::{OnceCell, RefCell},
    rc::Rc,
};

use flux_errors::{ErrorGuaranteed, E0999};
use itertools::Itertools;
use rustc_data_structures::unord::{ExtendUnord, UnordMap};
use rustc_errors::Diagnostic;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_macros::{Decodable, Encodable};
use rustc_span::{Span, Symbol};
use rustc_trait_selection::traits::NormalizeExt;

use crate::{
    fhir::{self, FluxLocalDefId},
    global_env::GlobalEnv,
    intern::List,
    pretty,
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

/// An error produced by a query.
///
/// We make a distinction between errors reported at def-site and errors reported at use-site.
///
/// For most errors reported at the def-site of an item, it makes little sense to check the definition
/// of dependent items. For example, if a function signature is ill-formed, checking the body of another
/// function that calls it, can produce confusing errors. In some cases, we can even fail to produce
/// a signature for a function in which case we can't even check its call sites. For these cases, we
/// emit an error at the definition site and return a [`QueryErr::Emitted`]. When checking a dependent,
/// we detect this and early return without reporting any errors at the use-site.
///
/// Other errors are better reported at the use-site. For example, if some code calls a function from
/// an external crate that has unsupported features, we ought to report the error at the call-site,
/// because it would be confusing to only mention the definition of the external function without
/// showing which part of the code is calling it. To attach a span to an error one can use [`QueryErr::at`]
/// to get a [`QueryErrAt`].
///
/// Both [`QueryErr`] and [`QueryErrAt`] implement [`Diagnostic`]. The implementation for [`QueryErr`]
/// reports the error at the definition site, while the implementation for [`QueryErrAt`] reports it at
/// the (attached) use-site span. This allows to play a bit lose because we can emit an error without
/// attatching a span, but this means we may forget to attach spans at some places. We should consider
/// not implementing [`Diagnostic`] for [`QueryErr`] such that we always make the distinction between
/// use-site and def-site explicit, e.g., we could have methods `QueryErr::at_use_site` and
/// `QueryErr::at_def_site` returning types with different implementations of [`Diagnostic`].
#[derive(Debug, Clone, Encodable, Decodable)]
pub enum QueryErr {
    Unsupported { def_id: DefId, err: UnsupportedErr },
    Ignored { def_id: DefId },
    InvalidGenericArg { def_id: DefId },
    InvalidAssocReft { impl_id: DefId, name: Symbol },
    Emitted(ErrorGuaranteed),
}

impl QueryErr {
    pub fn at(self, span: Span) -> QueryErrAt {
        QueryErrAt { span, err: self }
    }
}

/// See [`QueryErr`]
pub struct QueryErrAt {
    span: Span,
    err: QueryErr,
}

pub struct Providers {
    pub collect_specs: fn(GlobalEnv) -> crate::Specs,
    pub resolve_crate: fn(GlobalEnv) -> crate::ResolverOutput,
    pub desugar: for<'genv> fn(
        GlobalEnv<'genv, '_>,
        LocalDefId,
    ) -> QueryResult<UnordMap<LocalDefId, fhir::Node<'genv>>>,
    pub fhir_crate: for<'genv> fn(GlobalEnv<'genv, '_>) -> fhir::Crate<'genv>,
    pub qualifiers: fn(GlobalEnv) -> QueryResult<Vec<rty::Qualifier>>,
    pub spec_func_defns: fn(GlobalEnv) -> QueryResult<rty::SpecFuncDefns>,
    pub spec_func_decl: fn(GlobalEnv, Symbol) -> QueryResult<rty::SpecFuncDecl>,
    pub adt_sort_def_of: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::AdtSortDef>,
    pub check_wf: for<'genv> fn(GlobalEnv, FluxLocalDefId) -> QueryResult<Rc<rty::WfckResults>>,
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
    pub assoc_refinements_of: fn(GlobalEnv, LocalDefId) -> QueryResult<rty::AssocRefinements>,
    pub sort_of_assoc_reft:
        fn(GlobalEnv, LocalDefId, Symbol) -> QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>>,
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
            resolve_crate: |_| empty_query!(),
            desugar: |_, _| empty_query!(),
            fhir_crate: |_| empty_query!(),
            spec_func_defns: |_| empty_query!(),
            spec_func_decl: |_, _| empty_query!(),
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
    desugar: Cache<LocalDefId, QueryResult<fhir::Node<'genv>>>,
    fhir_crate: OnceCell<fhir::Crate<'genv>>,
    lower_generics_of: Cache<DefId, QueryResult<ty::Generics<'tcx>>>,
    lower_predicates_of: Cache<DefId, QueryResult<ty::GenericPredicates>>,
    lower_type_of: Cache<DefId, QueryResult<ty::EarlyBinder<ty::Ty>>>,
    lower_fn_sig: Cache<DefId, QueryResult<ty::EarlyBinder<ty::PolyFnSig>>>,
    defns: OnceCell<QueryResult<rty::SpecFuncDefns>>,
    func_decls: Cache<Symbol, QueryResult<rty::SpecFuncDecl>>,
    qualifiers: OnceCell<QueryResult<Vec<rty::Qualifier>>>,
    adt_sort_def_of: Cache<DefId, QueryResult<rty::AdtSortDef>>,
    check_wf: Cache<FluxLocalDefId, QueryResult<Rc<rty::WfckResults>>>,
    adt_def: Cache<DefId, QueryResult<rty::AdtDef>>,
    generics_of: Cache<DefId, QueryResult<rty::Generics>>,
    refinement_generics_of: Cache<DefId, QueryResult<rty::RefinementGenerics>>,
    predicates_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::GenericPredicates>>>,
    assoc_refinements_of: Cache<DefId, QueryResult<rty::AssocRefinements>>,
    assoc_refinement_def: Cache<(DefId, Symbol), QueryResult<rty::EarlyBinder<rty::Lambda>>>,
    sort_of_assoc_reft:
        Cache<(DefId, Symbol), QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>>>,
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
            resolve_crate: Default::default(),
            desugar: Default::default(),
            fhir_crate: Default::default(),
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

    pub(crate) fn desugar(
        &'genv self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
    ) -> QueryResult<fhir::Node<'genv>> {
        if let Some(v) = self.desugar.borrow().get(&def_id) {
            return v.clone();
        }
        match (self.providers.desugar)(genv, def_id) {
            Ok(nodes) => {
                let mut cache = self.desugar.borrow_mut();
                cache.extend_unord(nodes.into_items().map(|(def_id, node)| (def_id, Ok(node))));
                cache[&def_id].clone()
            }
            Err(err) => {
                self.desugar.borrow_mut().insert(def_id, Err(err.clone()));
                Err(err)
            }
        }
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
                .map_err(|err| QueryErr::unsupported(def_id, err))
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
                .map_err(|err| QueryErr::unsupported(def_id, err))
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
                    .map_err(|err| QueryErr::unsupported(def_id, err))?,
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
                    .map_err(|err| QueryErr::unsupported(def_id, err))?,
            ))
        })
    }

    pub(crate) fn spec_func_defns(&self, genv: GlobalEnv) -> QueryResult<&rty::SpecFuncDefns> {
        self.defns
            .get_or_init(|| (self.providers.spec_func_defns)(genv))
            .as_ref()
            .map_err(Clone::clone)
    }

    pub(crate) fn func_decl(
        &self,
        genv: GlobalEnv,
        name: Symbol,
    ) -> QueryResult<rty::SpecFuncDecl> {
        run_with_cache(&self.func_decls, name, || (self.providers.spec_func_decl)(genv, name))
    }

    pub(crate) fn qualifiers(&self, genv: GlobalEnv) -> QueryResult<&[rty::Qualifier]> {
        self.qualifiers
            .get_or_init(|| (self.providers.qualifiers)(genv))
            .as_deref()
            .map_err(Clone::clone)
    }

    pub(crate) fn adt_sort_def_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::AdtSortDef> {
        run_with_cache(&self.adt_sort_def_of, def_id, || {
            let extern_id = lookup_extern(genv, def_id);
            let def_id = extern_id.unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.adt_sort_def_of)(genv, local_id)
            } else if let Some(adt_sort_def) = genv.cstore().adt_sort_def(def_id) {
                adt_sort_def
            } else {
                Ok(rty::AdtSortDef::new(def_id, vec![], vec![]))
            }
        })
    }

    pub(crate) fn check_wf(
        &self,
        genv: GlobalEnv<'genv, '_>,
        flux_id: FluxLocalDefId,
    ) -> QueryResult<Rc<rty::WfckResults>> {
        run_with_cache(&self.check_wf, flux_id, || (self.providers.check_wf)(genv, flux_id))
    }

    pub(crate) fn adt_def(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<rty::AdtDef> {
        run_with_cache(&self.adt_def, def_id, || {
            let extern_id = lookup_extern(genv, def_id);
            let def_id = extern_id.unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.adt_def)(genv, local_id)
            } else if let Some(adt_def) = genv.cstore().adt_def(def_id) {
                adt_def
            } else {
                let adt_def = if let Some(extern_id) = extern_id {
                    lowering::lower_adt_def(genv.tcx(), genv.tcx().adt_def(extern_id))
                } else {
                    lowering::lower_adt_def(genv.tcx(), genv.tcx().adt_def(def_id))
                };
                Ok(rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id)?, vec![], false))
            }
        })
    }

    pub(crate) fn generics_of(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<rty::Generics> {
        run_with_cache(&self.generics_of, def_id, || {
            let def_id = lookup_extern(genv, def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.generics_of)(genv, local_id)
            } else if let Some(generics) = genv.cstore().generics_of(def_id) {
                generics
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
            let def_id = lookup_extern(genv, def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.refinement_generics_of)(genv, local_id)
            } else if let Some(refinement_generics) = genv.cstore().refinement_generics_of(def_id) {
                refinement_generics
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
            let def_id = lookup_extern(genv, def_id).unwrap_or(def_id);

            if let Some(local_id) = def_id.as_local() {
                (self.providers.item_bounds)(genv, local_id)
            } else if let Some(bounds) = genv.cstore().item_bounds(def_id) {
                bounds
            } else {
                let bounds = genv.tcx().item_bounds(def_id).skip_binder();
                let clauses = lowering::lower_item_bounds(genv.tcx(), bounds)
                    .map_err(|err| QueryErr::unsupported(def_id, err))?;

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
            let def_id = lookup_extern(genv, def_id).unwrap_or(def_id);

            if let Some(local_id) = def_id.as_local() {
                (self.providers.predicates_of)(genv, local_id)
            } else if let Some(predicates) = genv.cstore().predicates_of(def_id) {
                predicates
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
    ) -> QueryResult<rty::AssocRefinements> {
        run_with_cache(&self.assoc_refinements_of, def_id, || {
            let def_id = lookup_extern(genv, def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.assoc_refinements_of)(genv, local_id)
            } else if let Some(assocs) = genv.cstore().assoc_refinements_of(def_id) {
                assocs
            } else {
                Ok(rty::AssocRefinements::default())
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
            let impl_id = lookup_extern(genv, impl_id).unwrap_or(impl_id);
            if let Some(local_id) = impl_id.as_local() {
                (self.providers.assoc_refinement_def)(genv, local_id, name)
            } else if let Some(lam) = genv.cstore().assoc_refinements_def(impl_id, name) {
                lam
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
    ) -> QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>> {
        run_with_cache(&self.sort_of_assoc_reft, (def_id, name), || {
            let impl_id = lookup_extern(genv, def_id).unwrap_or(def_id);
            if let Some(local_id) = impl_id.as_local() {
                (self.providers.sort_of_assoc_reft)(genv, local_id, name)
            } else if let Some(sort) = genv.cstore().sort_of_assoc_reft(def_id, name) {
                sort
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
                ty
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
            let (def_id, _is_extern) = match lookup_extern(genv, def_id) {
                Some(def_id) => (def_id, true),
                None => (def_id, false),
            };
            if let Some(local_id) = def_id.as_local() {
                (self.providers.variants_of)(genv, local_id)
            } else if let Some(variants) = genv.cstore().variants(def_id) {
                variants.map(|variants| variants.map(|variants| variants.map(List::from)))
            } else {
                let variants = genv
                    .tcx()
                    .adt_def(def_id)
                    .variants()
                    .indices()
                    .map(|variant_idx| {
                        Refiner::default(genv, &genv.generics_of(def_id)?)
                            .refine_variant_def(def_id, variant_idx)
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
            let def_id = lookup_extern(genv, def_id).unwrap_or(def_id);
            if let Some(local_id) = def_id.as_local() {
                (self.providers.fn_sig)(genv, local_id)
            } else if let Some(fn_sig) = genv.cstore().fn_sig(def_id) {
                fn_sig
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
            let hir_id = genv.tcx().local_def_id_to_hir_id(def_id);
            let bound_vars = genv.tcx().late_bound_vars(hir_id);
            lowering::lower_bound_vars(bound_vars)
                .map_err(UnsupportedReason::into_err)
                .map_err(|err| QueryErr::unsupported(def_id.to_def_id(), err))
        })
    }
}

fn lookup_extern(genv: GlobalEnv, extern_def_id: DefId) -> Option<DefId> {
    genv.get_local_id_for_extern(extern_def_id)
        .map(LocalDefId::to_def_id)
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
    pub fn unsupported(def_id: DefId, err: UnsupportedErr) -> Self {
        QueryErr::Unsupported { def_id, err }
    }
}

impl<'a> Diagnostic<'a> for QueryErr {
    fn into_diag(
        self,
        dcx: rustc_errors::DiagCtxtHandle<'a>,
        _level: rustc_errors::Level,
    ) -> rustc_errors::Diag<'a, ErrorGuaranteed> {
        use crate::fluent_generated as fluent;

        rustc_middle::ty::tls::with(|tcx| {
            match self {
                QueryErr::Unsupported { def_id, err } => {
                    let span = err.span.unwrap_or_else(|| tcx.def_span(def_id));
                    let mut diag = dcx.struct_span_err(span, fluent::middle_query_unsupported);
                    diag.code(E0999);
                    diag.note(err.descr);
                    diag
                }
                QueryErr::Ignored { def_id } => {
                    let def_span = tcx.def_span(def_id);
                    let mut diag = dcx.struct_span_err(def_span, fluent::middle_query_ignored_item);
                    diag.code(E0999);
                    diag
                }
                QueryErr::InvalidGenericArg { def_id } => {
                    let def_span = tcx.def_span(def_id);
                    let mut diag =
                        dcx.struct_span_err(def_span, fluent::middle_query_invalid_generic_arg);
                    diag.code(E0999);
                    diag
                }
                QueryErr::Emitted(_) => {
                    let mut diag = dcx.struct_err("QueryErr::Emitted should be emitted");
                    diag.downgrade_to_delayed_bug();
                    diag
                }
                QueryErr::InvalidAssocReft { impl_id, name } => {
                    let def_span = tcx.def_span(impl_id);
                    let mut diag =
                        dcx.struct_span_err(def_span, fluent::middle_query_invalid_assoc_reft);
                    diag.arg("name", name);
                    diag.code(E0999);
                    diag
                }
            }
        })
    }
}

impl<'a> Diagnostic<'a> for QueryErrAt {
    fn into_diag(
        self,
        dcx: rustc_errors::DiagCtxtHandle<'a>,
        level: rustc_errors::Level,
    ) -> rustc_errors::Diag<'a, ErrorGuaranteed> {
        use crate::fluent_generated as fluent;

        rustc_middle::ty::tls::with(|tcx| {
            let mut diag = match self.err {
                QueryErr::Unsupported { def_id, err, .. } => {
                    let mut diag =
                        dcx.struct_span_err(self.span, fluent::middle_query_unsupported_at);
                    diag.arg("kind", tcx.def_kind(def_id).descr(def_id));
                    if let Some(def_ident_span) = tcx.def_ident_span(def_id) {
                        diag.span_note(def_ident_span, fluent::_subdiag::note);
                    }
                    diag.note(err.descr);
                    diag
                }
                QueryErr::Ignored { def_id } => {
                    let mut diag = dcx.struct_span_err(self.span, fluent::middle_query_ignored_at);
                    diag.arg("kind", tcx.def_kind(def_id).descr(def_id));
                    diag.arg("name", pretty::def_id_to_string(def_id));
                    diag.span_label(self.span, fluent::_subdiag::label);
                    diag
                }
                QueryErr::InvalidAssocReft { .. } => {
                    let mut diag =
                        dcx.struct_span_err(self.span, fluent::middle_query_invalid_assoc_reft_at);
                    diag.code(E0999);
                    diag
                }
                QueryErr::InvalidGenericArg { .. } | QueryErr::Emitted(_) => {
                    let mut diag = self.err.into_diag(dcx, level);
                    diag.span(self.span);
                    diag
                }
            };
            diag.code(E0999);
            diag
        })
    }
}

impl From<ErrorGuaranteed> for QueryErr {
    fn from(err: ErrorGuaranteed) -> Self {
        Self::Emitted(err)
    }
}
