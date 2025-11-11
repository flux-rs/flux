use std::{
    cell::{OnceCell, RefCell},
    rc::Rc,
};

use flux_arc_interner::List;
use flux_common::{bug, tracked_span_bug};
use flux_errors::{E0999, ErrorGuaranteed};
use flux_rustc_bridge::{
    self, def_id_to_string,
    lowering::{self, Lower, UnsupportedErr},
    mir, ty,
};
use itertools::Itertools;
use rustc_data_structures::unord::{ExtendUnord, UnordMap};
use rustc_errors::Diagnostic;
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_index::IndexVec;
use rustc_macros::{Decodable, Encodable};
use rustc_span::{Span, Symbol};

use crate::{
    def_id::{FluxDefId, FluxId, MaybeExternId, ResolvedDefId},
    fhir,
    global_env::GlobalEnv,
    rty::{
        self,
        refining::{self, Refine, Refiner},
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
/// the (attached) use-site span. This allows us to play a bit lose because we can emit an error without
/// attaching a span, but this means we may forget to attach spans at some places. We should consider
/// not implementing [`Diagnostic`] for [`QueryErr`] such that we always make the distinction between
/// use-site and def-site explicit, e.g., we could have methods `QueryErr::at_use_site` and
/// `QueryErr::at_def_site` returning types with different implementations of [`Diagnostic`].
#[derive(Debug, Clone, Encodable, Decodable)]
pub enum QueryErr {
    Unsupported {
        def_id: DefId,
        err: UnsupportedErr,
    },
    Ignored {
        def_id: DefId,
    },
    InvalidGenericArg {
        def_id: DefId,
    },
    MissingAssocReft {
        impl_id: DefId,
        trait_id: DefId,
        name: Symbol,
    },
    /// An operation tried to access the internals of an opaque struct.
    OpaqueStruct {
        struct_id: DefId,
    },
    /// Used to report bugs, typically this means executing an arm in a match we thought it was
    /// unreachable. Use this instead of panicking if it is easy to return a [`QueryErr`]. Use
    /// [`QueryErr::bug`] or [`crate::query_bug!`] to construct this variant to track source location.
    Bug {
        def_id: Option<DefId>,
        location: String,
        msg: String,
    },
    Emitted(ErrorGuaranteed),
}

#[macro_export]
macro_rules! query_bug {
    ($fmt:literal $(,$args:expr)* $(,)?) => {
        $crate::queries::QueryErr::bug(None, format_args!($fmt, $($args),*))
    };
    ($def_id:expr, $fmt:literal $(,$args:expr)* $(,)? ) => {{
        $crate::queries::QueryErr::bug(Some($def_id.into()), format_args!($fmt, $($args),*))
    }};
}

impl QueryErr {
    pub fn unsupported(def_id: DefId, err: UnsupportedErr) -> Self {
        QueryErr::Unsupported { def_id, err }
    }

    #[track_caller]
    pub fn bug(def_id: Option<DefId>, msg: impl ToString) -> Self {
        QueryErr::Bug {
            def_id,
            location: format!("{}", std::panic::Location::caller()),
            msg: msg.to_string(),
        }
    }

    pub fn at(self, cx: impl Into<ErrCtxt>) -> QueryErrAt {
        QueryErrAt { cx: cx.into(), err: self }
    }
}

/// A [`QueryErr`] with extra context information
pub struct QueryErrAt {
    cx: ErrCtxt,
    err: QueryErr,
}

/// The "use site" context in which an error is reported
#[derive(Clone, Copy)]
pub enum ErrCtxt {
    /// The error was triggered when checking a function body. The `Span` is the span in
    /// the mir associated with the error. The `LocalDefId` is the id of the function.
    FnCheck(Span, LocalDefId),
    /// A miscellaneous context for which we only have a span
    Misc(Span),
}

impl From<Span> for ErrCtxt {
    fn from(v: Span) -> Self {
        Self::Misc(v)
    }
}

impl ErrCtxt {
    fn span(self) -> Span {
        match self {
            ErrCtxt::Misc(span) => span,
            ErrCtxt::FnCheck(span, _) => span,
        }
    }
}

pub struct Providers {
    pub collect_specs: fn(GlobalEnv) -> crate::Specs,
    pub resolve_crate: fn(GlobalEnv) -> crate::ResolverOutput,
    pub desugar: for<'genv> fn(
        GlobalEnv<'genv, '_>,
        LocalDefId,
    ) -> QueryResult<UnordMap<LocalDefId, fhir::Node<'genv>>>,
    pub fhir_attr_map: for<'genv> fn(GlobalEnv<'genv, '_>, LocalDefId) -> fhir::AttrMap<'genv>,
    pub fhir_crate: for<'genv> fn(GlobalEnv<'genv, '_>) -> fhir::FluxItems<'genv>,
    pub qualifiers: fn(GlobalEnv) -> QueryResult<Vec<rty::Qualifier>>,
    pub prim_rel: fn(GlobalEnv) -> QueryResult<UnordMap<rty::BinOp, rty::PrimRel>>,
    pub normalized_defns: fn(GlobalEnv) -> rty::NormalizedDefns,
    pub func_sort: fn(GlobalEnv, FluxId<MaybeExternId>) -> rty::PolyFuncSort,
    pub func_span: fn(GlobalEnv, FluxId<MaybeExternId>) -> Span,
    pub adt_sort_def_of: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::AdtSortDef>,
    pub check_wf: fn(GlobalEnv, LocalDefId) -> QueryResult<Rc<rty::WfckResults>>,
    pub adt_def: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::AdtDef>,
    pub constant_info: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::ConstantInfo>,
    pub type_of: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::EarlyBinder<rty::TyOrCtor>>,
    pub variants_of: fn(
        GlobalEnv,
        MaybeExternId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>,
    pub fn_sig: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>>,
    pub generics_of: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::Generics>,
    pub refinement_generics_of:
        fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::EarlyBinder<rty::RefinementGenerics>>,
    pub predicates_of:
        fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>>,
    pub assoc_refinements_of: fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::AssocRefinements>,
    pub sort_of_assoc_reft:
        fn(GlobalEnv, FluxId<MaybeExternId>) -> QueryResult<rty::EarlyBinder<rty::FuncSort>>,
    pub assoc_refinement_body:
        fn(GlobalEnv, FluxId<MaybeExternId>) -> QueryResult<rty::EarlyBinder<rty::Lambda>>,
    #[allow(clippy::type_complexity)]
    pub default_assoc_refinement_body:
        fn(GlobalEnv, FluxId<MaybeExternId>) -> QueryResult<Option<rty::EarlyBinder<rty::Lambda>>>,
    pub item_bounds:
        fn(GlobalEnv, MaybeExternId) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>>,
    pub sort_decl_param_count: fn(GlobalEnv, FluxId<MaybeExternId>) -> usize,
    pub no_panic: fn(GlobalEnv, MaybeExternId) -> QueryResult<bool>,
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
            fhir_attr_map: |_, _| empty_query!(),
            fhir_crate: |_| empty_query!(),
            normalized_defns: |_| empty_query!(),
            func_sort: |_, _| empty_query!(),
            func_span: |_, _| empty_query!(),
            qualifiers: |_| empty_query!(),
            prim_rel: |_| empty_query!(),
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
            assoc_refinement_body: |_, _| empty_query!(),
            default_assoc_refinement_body: |_, _| empty_query!(),
            sort_of_assoc_reft: |_, _| empty_query!(),
            item_bounds: |_, _| empty_query!(),
            constant_info: |_, _| empty_query!(),
            sort_decl_param_count: |_, _| empty_query!(),
            no_panic: |_, _| empty_query!(),
        }
    }
}

pub struct Queries<'genv, 'tcx> {
    pub(crate) providers: Providers,
    mir: Cache<LocalDefId, QueryResult<Rc<mir::Body<'tcx>>>>,
    collect_specs: OnceCell<crate::Specs>,
    resolve_crate: OnceCell<crate::ResolverOutput>,
    desugar: Cache<LocalDefId, QueryResult<fhir::Node<'genv>>>,
    fhir_attr_map: Cache<LocalDefId, fhir::AttrMap<'genv>>,
    fhir_crate: OnceCell<fhir::FluxItems<'genv>>,
    lower_generics_of: Cache<DefId, ty::Generics<'tcx>>,
    lower_predicates_of: Cache<DefId, QueryResult<ty::GenericPredicates>>,
    lower_type_of: Cache<DefId, QueryResult<ty::EarlyBinder<ty::Ty>>>,
    lower_fn_sig: Cache<DefId, QueryResult<ty::EarlyBinder<ty::PolyFnSig>>>,
    normalized_defns: Cache<CrateNum, Rc<rty::NormalizedDefns>>,
    func_sort: Cache<FluxDefId, rty::PolyFuncSort>,
    func_span: Cache<FluxDefId, Span>,
    qualifiers: OnceCell<QueryResult<Vec<rty::Qualifier>>>,
    prim_rel: OnceCell<QueryResult<UnordMap<rty::BinOp, rty::PrimRel>>>,
    adt_sort_def_of: Cache<DefId, QueryResult<rty::AdtSortDef>>,
    check_wf: Cache<LocalDefId, QueryResult<Rc<rty::WfckResults>>>,
    adt_def: Cache<DefId, QueryResult<rty::AdtDef>>,
    constant_info: Cache<DefId, QueryResult<rty::ConstantInfo>>,
    generics_of: Cache<DefId, QueryResult<rty::Generics>>,
    refinement_generics_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::RefinementGenerics>>>,
    predicates_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::GenericPredicates>>>,
    assoc_refinements_of: Cache<DefId, QueryResult<rty::AssocRefinements>>,
    assoc_refinement_body: Cache<FluxDefId, QueryResult<rty::EarlyBinder<rty::Lambda>>>,
    default_assoc_refinement_body:
        Cache<FluxDefId, QueryResult<Option<rty::EarlyBinder<rty::Lambda>>>>,
    sort_of_assoc_reft: Cache<FluxDefId, QueryResult<rty::EarlyBinder<rty::FuncSort>>>,
    item_bounds: Cache<DefId, QueryResult<rty::EarlyBinder<List<rty::Clause>>>>,
    type_of: Cache<DefId, QueryResult<rty::EarlyBinder<rty::TyOrCtor>>>,
    variants_of: Cache<DefId, QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>>,
    fn_sig: Cache<DefId, QueryResult<rty::EarlyBinder<rty::PolyFnSig>>>,
    lower_late_bound_vars: Cache<LocalDefId, QueryResult<List<ty::BoundVariableKind>>>,
    sort_decl_param_count: Cache<FluxDefId, usize>,
    no_panic: Cache<DefId, QueryResult<bool>>,
}

impl<'genv, 'tcx> Queries<'genv, 'tcx> {
    pub(crate) fn new(providers: Providers) -> Self {
        Self {
            providers,
            mir: Default::default(),
            collect_specs: Default::default(),
            resolve_crate: Default::default(),
            desugar: Default::default(),
            fhir_attr_map: Default::default(),
            fhir_crate: Default::default(),
            lower_generics_of: Default::default(),
            lower_predicates_of: Default::default(),
            lower_type_of: Default::default(),
            lower_fn_sig: Default::default(),
            normalized_defns: Default::default(),
            func_sort: Default::default(),
            func_span: Default::default(),
            qualifiers: Default::default(),
            prim_rel: Default::default(),
            adt_sort_def_of: Default::default(),
            check_wf: Default::default(),
            adt_def: Default::default(),
            constant_info: Default::default(),
            generics_of: Default::default(),
            refinement_generics_of: Default::default(),
            predicates_of: Default::default(),
            assoc_refinements_of: Default::default(),
            assoc_refinement_body: Default::default(),
            default_assoc_refinement_body: Default::default(),
            sort_of_assoc_reft: Default::default(),
            item_bounds: Default::default(),
            type_of: Default::default(),
            variants_of: Default::default(),
            fn_sig: Default::default(),
            lower_late_bound_vars: Default::default(),
            sort_decl_param_count: Default::default(),
            no_panic: Default::default(),
        }
    }

    pub(crate) fn mir(
        &self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
    ) -> QueryResult<Rc<mir::Body<'tcx>>> {
        run_with_cache(&self.mir, def_id, || {
            let mir = unsafe { flux_common::mir_storage::retrieve_mir_body(genv.tcx(), def_id) };
            let mir =
                lowering::MirLoweringCtxt::lower_mir_body(genv.tcx(), genv.sess(), def_id, mir)?;
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
                let Some(res) = cache.get(&def_id) else {
                    tracked_span_bug!("cannot desugar {def_id:?}")
                };
                res.clone()
            }
            Err(err) => {
                self.desugar.borrow_mut().insert(def_id, Err(err.clone()));
                Err(err)
            }
        }
    }

    pub(crate) fn fhir_attr_map(
        &'genv self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
    ) -> fhir::AttrMap<'genv> {
        run_with_cache(&self.fhir_attr_map, def_id, || (self.providers.fhir_attr_map)(genv, def_id))
    }

    pub(crate) fn fhir_crate(
        &'genv self,
        genv: GlobalEnv<'genv, 'tcx>,
    ) -> &'genv fhir::FluxItems<'genv> {
        self.fhir_crate
            .get_or_init(|| (self.providers.fhir_crate)(genv))
    }

    pub(crate) fn lower_generics_of(
        &self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: DefId,
    ) -> ty::Generics<'tcx> {
        run_with_cache(&self.lower_generics_of, def_id, || {
            genv.tcx().generics_of(def_id).lower(genv.tcx())
        })
    }

    pub(crate) fn lower_predicates_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::GenericPredicates> {
        run_with_cache(&self.lower_predicates_of, def_id, || {
            genv.tcx()
                .predicates_of(def_id)
                .lower(genv.tcx())
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
                ty.lower(genv.tcx())
                    .map_err(|err| QueryErr::unsupported(def_id, err.into_err()))?,
            ))
        })
    }

    pub(crate) fn lower_fn_sig(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        run_with_cache(&self.lower_fn_sig, def_id, || {
            let fn_sig = genv.tcx().fn_sig(def_id).instantiate_identity();
            Ok(ty::EarlyBinder(
                fn_sig
                    .lower(genv.tcx())
                    .map_err(|err| QueryErr::unsupported(def_id, err.into_err()))?,
            ))
        })
    }

    pub(crate) fn lower_late_bound_vars(
        &self,
        genv: GlobalEnv,
        def_id: LocalDefId,
    ) -> QueryResult<List<ty::BoundVariableKind>> {
        run_with_cache(&self.lower_late_bound_vars, def_id, || {
            let hir_id = genv.tcx().local_def_id_to_hir_id(def_id);
            genv.tcx()
                .late_bound_vars(hir_id)
                .lower(genv.tcx())
                .map_err(|err| QueryErr::unsupported(def_id.to_def_id(), err.into_err()))
        })
    }

    pub(crate) fn normalized_defns(
        &self,
        genv: GlobalEnv,
        krate: CrateNum,
    ) -> Rc<rty::NormalizedDefns> {
        run_with_cache(&self.normalized_defns, krate, || {
            if krate == LOCAL_CRATE {
                Rc::new((self.providers.normalized_defns)(genv))
            } else {
                genv.cstore().normalized_defns(krate)
            }
        })
    }

    pub(crate) fn func_sort(&self, genv: GlobalEnv, def_id: FluxDefId) -> rty::PolyFuncSort {
        run_with_cache(&self.func_sort, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| {
                    // refinement functions cannot be extern specs so we simply grab the local id
                    (self.providers.func_sort)(genv, def_id)
                },
                |def_id| genv.cstore().func_sort(def_id),
                |_| {
                    bug!(
                        "cannot generate default function sort, the refinement must be defined somewhere"
                    )
                },
            )
        })
    }

    pub(crate) fn func_span(&self, genv: GlobalEnv, def_id: FluxDefId) -> Span {
        run_with_cache(&self.func_span, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| {
                    // refinement functions cannot be extern specs so we simply grab the local id
                    (self.providers.func_span)(genv, def_id)
                },
                |def_id| genv.cstore().func_span(def_id),
                |_|
                bug!(
                        "cannot generate default function sort, the refinement must be defined somewhere"
                    )
                ,
            )
        })
    }

    pub(crate) fn qualifiers(&self, genv: GlobalEnv) -> QueryResult<&[rty::Qualifier]> {
        self.qualifiers
            .get_or_init(|| (self.providers.qualifiers)(genv))
            .as_deref()
            .map_err(Clone::clone)
    }

    pub(crate) fn prim_rel(
        &self,
        genv: GlobalEnv,
    ) -> QueryResult<&UnordMap<rty::BinOp, rty::PrimRel>> {
        self.prim_rel
            .get_or_init(|| (self.providers.prim_rel)(genv))
            .as_ref()
            .map_err(|err| err.clone())
    }

    pub(crate) fn adt_sort_def_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::AdtSortDef> {
        run_with_cache(&self.adt_sort_def_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.adt_sort_def_of)(genv, def_id),
                |def_id| genv.cstore().adt_sort_def(def_id),
                |def_id| {
                    let variants = IndexVec::from([rty::AdtSortVariant::new(vec![])]);
                    Ok(rty::AdtSortDef::new(def_id, vec![], variants, false, true))
                },
            )
        })
    }

    pub(crate) fn sort_decl_param_count(&self, genv: GlobalEnv, def_id: FluxDefId) -> usize {
        run_with_cache(&self.sort_decl_param_count, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| {
                    (self.providers.sort_decl_param_count)(genv, def_id)
                },
                |def_id| genv.cstore().sort_decl_param_count(def_id),
                |_| {
                    bug!(
                        "cannot generate default param count for sort declaration, it must be defined somewhere"
                    )
                }
            )
        })
    }

    pub(crate) fn check_wf(
        &self,
        genv: GlobalEnv<'genv, '_>,
        def_id: LocalDefId,
    ) -> QueryResult<Rc<rty::WfckResults>> {
        run_with_cache(&self.check_wf, def_id, || (self.providers.check_wf)(genv, def_id))
    }

    pub(crate) fn constant_info(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::ConstantInfo> {
        run_with_cache(&self.constant_info, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.constant_info)(genv, def_id),
                |def_id| genv.cstore().constant_info(def_id),
                |def_id| {
                    // TODO(RJ): fix duplication with [`conv_constant`]` in `flux-fhir-analysis`
                    let ty = genv.tcx().type_of(def_id).no_bound_vars().unwrap();
                    if ty.is_integral() {
                        let val = genv.tcx().const_eval_poly(def_id).ok().and_then(|val| {
                            let val = val.try_to_scalar_int()?;
                            rty::Constant::from_scalar_int(genv.tcx(), val, &ty)
                        });
                        if let Some(constant_) = val {
                            return Ok(rty::ConstantInfo::Interpreted(
                                rty::Expr::constant(constant_),
                                rty::Sort::Int,
                            ));
                        }
                    }
                    Ok(rty::ConstantInfo::Uninterpreted)
                },
            )
        })
    }

    pub(crate) fn no_panic(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<bool> {
        run_with_cache(&self.no_panic, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| {
                    match def_id {
                        MaybeExternId::Local(def_id) => Ok(genv.fhir_attr_map(def_id).no_panic()),
                        MaybeExternId::Extern(def_id, _) => {
                            Ok(genv.fhir_attr_map(def_id).no_panic())
                        },
                    }
                },
                |def_id| genv.cstore().no_panic(def_id),
                |def_id| {
                    genv.cstore().no_panic(def_id).unwrap_or(Ok(false))
                },
            )
        })
    }

    pub(crate) fn adt_def(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<rty::AdtDef> {
        run_with_cache(&self.adt_def, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.adt_def)(genv, def_id),
                |def_id| genv.cstore().adt_def(def_id),
                |def_id| {
                    let adt_def = genv.tcx().adt_def(def_id).lower(genv.tcx());
                    Ok(rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id)?, vec![], false))
                },
            )
        })
    }

    pub(crate) fn generics_of(&self, genv: GlobalEnv, def_id: DefId) -> QueryResult<rty::Generics> {
        run_with_cache(&self.generics_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.generics_of)(genv, def_id),
                |def_id| genv.cstore().generics_of(def_id),
                |def_id| {
                    Ok(refining::refine_generics(genv, def_id, &genv.lower_generics_of(def_id)))
                },
            )
        })
    }

    pub(crate) fn refinement_generics_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::RefinementGenerics>> {
        run_with_cache(&self.refinement_generics_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.refinement_generics_of)(genv, def_id),
                |def_id| genv.cstore().refinement_generics_of(def_id),
                |def_id| {
                    let parent = genv.tcx().generics_of(def_id).parent;
                    Ok(rty::EarlyBinder(rty::RefinementGenerics {
                        parent,
                        parent_count: 0,
                        own_params: List::empty(),
                    }))
                },
            )
        })
    }

    pub(crate) fn item_bounds(
        &self,
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
        run_with_cache(&self.item_bounds, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.item_bounds)(genv, def_id),
                |def_id| genv.cstore().item_bounds(def_id),
                |def_id| {
                    let clauses = genv
                        .tcx()
                        .item_bounds(def_id)
                        .skip_binder()
                        .lower(genv.tcx())
                        .map_err(|err| QueryErr::unsupported(def_id, err))?
                        .refine(&Refiner::default_for_item(genv, def_id)?)?;

                    Ok(rty::EarlyBinder(clauses))
                },
            )
        })
    }

    pub(crate) fn predicates_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        run_with_cache(&self.predicates_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.predicates_of)(genv, def_id),
                |def_id| genv.cstore().predicates_of(def_id),
                |def_id| {
                    let predicates = genv
                        .lower_predicates_of(def_id)?
                        .refine(&Refiner::default_for_item(genv, def_id)?)?;
                    Ok(rty::EarlyBinder(predicates))
                },
            )
        })
    }

    pub(crate) fn assoc_refinements_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::AssocRefinements> {
        run_with_cache(&self.assoc_refinements_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.assoc_refinements_of)(genv, def_id),
                |def_id| genv.cstore().assoc_refinements_of(def_id),
                |_| Ok(rty::AssocRefinements::default()),
            )
        })
    }

    pub(crate) fn assoc_refinement_body(
        &self,
        genv: GlobalEnv,
        impl_assoc_id: FluxDefId,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        run_with_cache(&self.assoc_refinement_body, impl_assoc_id, || {
            impl_assoc_id.dispatch_query(
                genv,
                |impl_assoc_id| (self.providers.assoc_refinement_body)(genv, impl_assoc_id),
                |impl_assoc_id| genv.cstore().assoc_refinements_def(impl_assoc_id),
                |impl_assoc_id| {
                    Err(query_bug!(
                        impl_assoc_id.parent(),
                        "cannot generate default associate refinement for extern impl"
                    ))
                },
            )
        })
    }

    pub(crate) fn default_assoc_refinement_body(
        &self,
        genv: GlobalEnv,
        trait_assoc_id: FluxDefId,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::Lambda>>> {
        run_with_cache(&self.default_assoc_refinement_body, trait_assoc_id, || {
            trait_assoc_id.dispatch_query(
                genv,
                |trait_assoc_id| {
                    (self.providers.default_assoc_refinement_body)(genv, trait_assoc_id)
                },
                |trait_assoc_id| genv.cstore().default_assoc_refinements_def(trait_assoc_id),
                |trait_assoc_id| {
                    Err(query_bug!(
                        trait_assoc_id.parent(),
                        "cannot generate default assoc refinement for extern trait"
                    ))
                },
            )
        })
    }

    pub(crate) fn sort_of_assoc_reft(
        &self,
        genv: GlobalEnv,
        assoc_id: FluxDefId,
    ) -> QueryResult<rty::EarlyBinder<rty::FuncSort>> {
        run_with_cache(&self.sort_of_assoc_reft, assoc_id, || {
            assoc_id.dispatch_query(
                genv,
                |assoc_id| (self.providers.sort_of_assoc_reft)(genv, assoc_id),
                |assoc_id| genv.cstore().sort_of_assoc_reft(assoc_id),
                |assoc_id| {
                    Err(query_bug!(
                        assoc_id.parent(),
                        "cannot generate default sort for assoc refinement in extern crate"
                    ))
                },
            )
        })
    }

    pub(crate) fn type_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::TyOrCtor>> {
        run_with_cache(&self.type_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.type_of)(genv, def_id),
                |def_id| genv.cstore().type_of(def_id),
                |def_id| {
                    // If we're given a type parameter, provide the generics of the parent container.
                    let generics_def_id = match genv.def_kind(def_id) {
                        DefKind::TyParam => genv.tcx().parent(def_id),
                        _ => def_id,
                    };
                    let ty = genv.lower_type_of(def_id)?.skip_binder();
                    Ok(rty::EarlyBinder(
                        Refiner::default_for_item(genv, generics_def_id)?
                            .refine_ty_or_base(&ty)?
                            .into(),
                    ))
                },
            )
        })
    }

    pub(crate) fn variants_of(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        run_with_cache(&self.variants_of, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.variants_of)(genv, def_id),
                |def_id| genv.cstore().variants_of(def_id),
                |def_id| {
                    let variants = genv
                        .tcx()
                        .adt_def(def_id)
                        .variants()
                        .indices()
                        .map(|variant_idx| {
                            Refiner::default_for_item(genv, def_id)?
                                .refine_variant_def(def_id, variant_idx)
                        })
                        .try_collect()?;
                    Ok(rty::Opaqueness::Transparent(rty::EarlyBinder(variants)))
                },
            )
        })
    }

    pub(crate) fn fn_sig(
        &self,
        genv: GlobalEnv,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        run_with_cache(&self.fn_sig, def_id, || {
            def_id.dispatch_query(
                genv,
                |def_id| (self.providers.fn_sig)(genv, def_id),
                |def_id| genv.cstore().fn_sig(def_id),
                |def_id| {
                    let fn_sig = genv
                        .lower_fn_sig(def_id)?
                        .skip_binder()
                        .refine(&Refiner::default_for_item(genv, def_id)?)?
                        .hoist_input_binders();
                    Ok(rty::EarlyBinder(fn_sig))
                },
            )
        })
    }
}

/// Logic to *dispatch* a `def_id` to a provider (`local`, `external`, or `default`).
/// This is a trait so it can be implemented for [`DefId`] and for [`FluxDefId`].
trait DispatchKey: Sized {
    type LocalId;

    fn dispatch_query<R>(
        self,
        genv: GlobalEnv,
        local: impl FnOnce(Self::LocalId) -> R,
        external: impl FnOnce(Self) -> Option<R>,
        default: impl FnOnce(Self) -> R,
    ) -> R;
}

impl DispatchKey for DefId {
    type LocalId = MaybeExternId;

    fn dispatch_query<R>(
        self,
        genv: GlobalEnv,
        local: impl FnOnce(MaybeExternId) -> R,
        external: impl FnOnce(Self) -> Option<R>,
        default: impl FnOnce(Self) -> R,
    ) -> R {
        match genv.resolve_id(self) {
            ResolvedDefId::Local(local_id) => {
                // Case 1: `def_id` is a `LocalDefId` so forward it to the *local provider*
                local(MaybeExternId::Local(local_id))
            }
            ResolvedDefId::ExternSpec(local_id, def_id) => {
                // Case 2: `def_id` is a `LocalDefId` wrapping an extern spec, so we also
                // forward it to the local provider
                local(MaybeExternId::Extern(local_id, def_id))
            }
            ResolvedDefId::Extern(def_id) if let Some(v) = external(def_id) => {
                // Case 3: `def_id` is an external `def_id` for which we have an annotation in the
                // *external provider*
                v
            }
            ResolvedDefId::Extern(def_id) => {
                // Case 4: If none of the above, we generate a default annotation
                default(def_id)
            }
        }
    }
}

impl DispatchKey for FluxDefId {
    type LocalId = FluxId<MaybeExternId>;

    fn dispatch_query<R>(
        self,
        genv: GlobalEnv,
        local: impl FnOnce(FluxId<MaybeExternId>) -> R,
        external: impl FnOnce(FluxId<DefId>) -> Option<R>,
        default: impl FnOnce(FluxId<DefId>) -> R,
    ) -> R {
        #[allow(
            clippy::disallowed_methods,
            reason = "we are mapping the parent id to a different representation which still guarantees the existence of the item"
        )]
        self.parent().dispatch_query(
            genv,
            |container_id| local(FluxId::new(container_id, self.name())),
            |container_id| external(FluxId::new(container_id, self.name())),
            |container_id| default(FluxId::new(container_id, self.name())),
        )
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

impl<'a> Diagnostic<'a> for QueryErr {
    #[track_caller]
    fn into_diag(
        self,
        dcx: rustc_errors::DiagCtxtHandle<'a>,
        _level: rustc_errors::Level,
    ) -> rustc_errors::Diag<'a, ErrorGuaranteed> {
        use crate::fluent_generated as fluent;

        rustc_middle::ty::tls::with_opt(
            #[track_caller]
            |tcx| {
                let tcx = tcx.expect("no TyCtxt stored in tls");
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
                        let mut diag =
                            dcx.struct_span_err(def_span, fluent::middle_query_ignored_item);
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
                    QueryErr::MissingAssocReft { impl_id, name, .. } => {
                        let def_span = tcx.def_span(impl_id);
                        let mut diag =
                            dcx.struct_span_err(def_span, fluent::middle_query_missing_assoc_reft);
                        diag.arg("name", name);
                        diag.code(E0999);
                        diag
                    }
                    QueryErr::Bug { def_id, location, msg } => {
                        let mut diag = dcx.struct_err(fluent::middle_query_bug);
                        if let Some(def_id) = def_id {
                            diag.span(tcx.def_span(def_id));
                        }
                        diag.arg("location", location);
                        diag.note(msg);
                        diag
                    }
                    QueryErr::Emitted(_) => {
                        let mut diag = dcx.struct_err("QueryErr::Emitted should be emitted");
                        diag.downgrade_to_delayed_bug();
                        diag
                    }
                    QueryErr::OpaqueStruct { struct_id } => {
                        let struct_span = tcx.def_span(struct_id);
                        let mut diag =
                            dcx.struct_span_err(struct_span, fluent::middle_query_opaque_struct);
                        diag.arg("struct", tcx.def_path_str(struct_id));
                        diag
                    }
                }
            },
        )
    }
}

impl<'a> Diagnostic<'a> for QueryErrAt {
    #[track_caller]
    fn into_diag(
        self,
        dcx: rustc_errors::DiagCtxtHandle<'a>,
        level: rustc_errors::Level,
    ) -> rustc_errors::Diag<'a, ErrorGuaranteed> {
        use crate::fluent_generated as fluent;

        rustc_middle::ty::tls::with_opt(
            #[track_caller]
            |tcx| {
                let tcx = tcx.expect("no TyCtxt stored in tls");
                let cx_span = self.cx.span();
                let mut diag = match self.err {
                    QueryErr::Unsupported { def_id, err, .. } => {
                        let mut diag =
                            dcx.struct_span_err(cx_span, fluent::middle_query_unsupported_at);
                        diag.arg("kind", tcx.def_kind(def_id).descr(def_id));
                        if let Some(def_ident_span) = tcx.def_ident_span(def_id) {
                            diag.span_note(def_ident_span, fluent::_subdiag::note);
                        }
                        diag.note(err.descr);
                        diag
                    }
                    QueryErr::Ignored { def_id } => {
                        let mut diag =
                            dcx.struct_span_err(cx_span, fluent::middle_query_ignored_at);
                        diag.arg("kind", tcx.def_kind(def_id).descr(def_id));
                        diag.arg("name", def_id_to_string(def_id));
                        diag.span_label(cx_span, fluent::_subdiag::label);
                        diag
                    }
                    QueryErr::MissingAssocReft { name, .. } => {
                        let mut diag = dcx
                            .struct_span_err(cx_span, fluent::middle_query_missing_assoc_reft_at);
                        diag.arg("name", name);
                        diag.code(E0999);
                        diag
                    }
                    QueryErr::OpaqueStruct { struct_id } => {
                        let mut diag =
                            dcx.struct_span_err(cx_span, fluent::middle_query_opaque_struct);
                        diag.arg("struct", tcx.def_path_str(struct_id));
                        diag.span_label(cx_span, fluent::_subdiag::label);
                        if let ErrCtxt::FnCheck(_, fn_def_id) = self.cx {
                            let fn_span = tcx.def_span(fn_def_id);
                            diag.arg("def_kind", tcx.def_descr(fn_def_id.to_def_id()));
                            diag.span_label(fn_span, fluent::middle_query_opaque_struct_help);
                            diag.note(fluent::middle_query_opaque_struct_note);
                        }
                        diag
                    }
                    QueryErr::InvalidGenericArg { .. }
                    | QueryErr::Emitted(_)
                    | QueryErr::Bug { .. } => {
                        let mut diag = self.err.into_diag(dcx, level);
                        diag.span(cx_span);
                        diag
                    }
                };
                diag.code(E0999);
                diag
            },
        )
    }
}

impl From<ErrorGuaranteed> for QueryErr {
    fn from(err: ErrorGuaranteed) -> Self {
        Self::Emitted(err)
    }
}

pub fn try_query<T>(f: impl FnOnce() -> QueryResult<T>) -> QueryResult<T> {
    f()
}
