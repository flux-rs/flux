use std::rc::Rc;

use flux_errors::FluxSession;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    LangItem,
};
use rustc_middle::ty::{TyCtxt, Variance};
pub use rustc_span::{symbol::Ident, Symbol};

use crate::{
    early_ctxt::EarlyCtxt,
    fhir::{self, FluxLocalDefId, VariantIdx},
    intern::List,
    queries::{Providers, Queries, QueryResult},
    rty::{self, fold::TypeFoldable, normalize::Defns, refining::Refiner},
    rustc,
};

pub struct GlobalEnv<'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'sess FluxSession,
    func_decls: FxHashMap<Symbol, rty::FuncDecl>,
    /// Names of 'local' qualifiers to be used when checking a given `DefId`.
    fn_quals: FxHashMap<DefId, FxHashSet<Symbol>>,
    early_cx: EarlyCtxt<'sess, 'tcx>,
    queries: Queries<'tcx>,
    extern_specs: FxHashMap<DefId, DefId>,
}

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
    pub fn new(
        early_cx: EarlyCtxt<'sess, 'tcx>,
        func_decls: FxHashMap<Symbol, rty::FuncDecl>,
        providers: Providers,
    ) -> Self {
        let mut fn_quals = FxHashMap::default();
        for (def_id, names) in early_cx.map.fn_quals() {
            let names = names.iter().map(|ident| ident.name).collect();
            fn_quals.insert(def_id.to_def_id(), names);
        }
        let externs = early_cx
            .map
            .externs()
            .iter()
            .map(|(extern_def_id, local_def_id)| (*extern_def_id, local_def_id.to_def_id()))
            .collect();
        GlobalEnv {
            tcx: early_cx.tcx,
            sess: early_cx.sess,
            early_cx,
            func_decls,
            fn_quals,
            queries: Queries::new(providers),
            extern_specs: externs,
        }
    }

    pub fn map(&self) -> &fhir::Map {
        &self.early_cx.map
    }

    pub fn defns(&self) -> QueryResult<&Defns> {
        self.queries.defns(self)
    }

    fn fn_quals(&self, did: DefId) -> FxHashSet<Symbol> {
        match self.fn_quals.get(&did) {
            None => FxHashSet::default(),
            Some(names) => names.clone(),
        }
    }

    pub fn qualifiers(&self, did: DefId) -> QueryResult<impl Iterator<Item = &rty::Qualifier>> {
        let names = self.fn_quals(did);
        Ok(self
            .queries
            .qualifiers(self)?
            .iter()
            .filter(move |qualifier| qualifier.global || names.contains(&qualifier.name)))
    }

    pub fn func_decls(&self) -> impl Iterator<Item = &rty::FuncDecl> {
        self.func_decls.values()
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn mk_box(&self, ty: rty::Ty, alloc: rty::Ty) -> rty::Ty {
        let def_id = self.tcx.require_lang_item(LangItem::OwnedBox, None);
        let adt_def = self.adt_def(def_id).unwrap();

        // this is harcoding that `Box` has two type parameters and
        // it is indexed by unit. We leave this as a reminder in case
        // that ever changes.
        debug_assert_eq!(self.generics_of(def_id).unwrap().params.len(), 2);
        debug_assert!(adt_def.sort().is_unit());

        let bty =
            rty::BaseTy::adt(adt_def, vec![rty::GenericArg::Ty(ty), rty::GenericArg::Ty(alloc)]);
        rty::Ty::indexed(bty, rty::Index::unit())
    }

    pub fn mir(&self, def_id: LocalDefId) -> QueryResult<Rc<rustc::mir::Body<'tcx>>> {
        self.queries.mir(self, def_id)
    }

    pub fn lower_type_of(&self, def_id: DefId) -> QueryResult<rustc::ty::Ty> {
        self.queries.lower_type_of(self, def_id)
    }

    pub fn lower_fn_sig(&self, def_id: DefId) -> QueryResult<rustc::ty::PolyFnSig> {
        self.queries.lower_fn_sig(self, def_id)
    }

    pub fn adt_def(&self, def_id: impl Into<DefId>) -> QueryResult<rty::AdtDef> {
        self.queries.adt_def(self, def_id.into())
    }

    pub fn check_wf(
        &self,
        flux_id: impl Into<FluxLocalDefId>,
    ) -> QueryResult<Rc<fhir::WfckResults>> {
        self.queries.check_wf(self, flux_id.into())
    }

    pub fn generics_of(&self, def_id: impl Into<DefId>) -> QueryResult<rty::Generics> {
        self.queries.generics_of(self, def_id.into())
    }

    pub fn predicates_of(
        &self,
        def_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        self.queries.predicates_of(self, def_id)
    }

    pub fn type_of(&self, def_id: DefId) -> QueryResult<rty::EarlyBinder<rty::PolyTy>> {
        self.queries.type_of(self, def_id)
    }

    pub fn fn_sig(&self, def_id: DefId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        self.queries.fn_sig(self, def_id)
    }

    pub fn variants_of(&self, def_id: DefId) -> QueryResult<rty::PolyVariants> {
        self.queries.variants_of(self, def_id)
    }

    pub fn variant(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariant>>> {
        Ok(self
            .variants_of(def_id)?
            .map(|variants| rty::EarlyBinder(variants[variant_idx.as_usize()].clone())))
    }

    pub fn late_bound_vars(&self, def_id: LocalDefId) -> QueryResult<List<rty::BoundVariableKind>> {
        self.queries.late_bound_vars(self, def_id)
    }

    pub fn index_sorts_of(&self, def_id: impl Into<DefId>) -> &[fhir::Sort] {
        self.early_cx.index_sorts_of(def_id.into())
    }

    pub fn early_bound_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        self.early_cx.early_bound_sorts_of(def_id)
    }

    pub fn refine_default(
        &self,
        generics: &rty::Generics,
        rustc_ty: &rustc::ty::Ty,
    ) -> QueryResult<rty::Ty> {
        Refiner::default(self, generics).refine_ty(rustc_ty)
    }

    pub fn refine_with_holes(
        &self,
        generics: &rty::Generics,
        rustc_ty: &rustc::ty::Ty,
    ) -> QueryResult<rty::Ty> {
        Refiner::with_holes(self, generics).refine_ty(rustc_ty)
    }

    pub fn instantiate_arg_for_fun(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        Refiner::new(self, generics, |bty| {
            let sort = bty.sort();
            let mut ty = rty::Ty::indexed(bty.shift_in_escaping(1), rty::Expr::nu());
            if !sort.is_unit() {
                ty = rty::Ty::constr(rty::Expr::hole(), ty);
            }
            rty::Binder::with_sort(ty, sort)
        })
        .refine_generic_arg(param, arg)
    }

    pub fn instantiate_arg_for_constructor(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        Refiner::with_holes(self, generics).refine_generic_arg(param, arg)
    }

    pub fn early_cx(&self) -> &EarlyCtxt<'sess, 'tcx> {
        &self.early_cx
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }

    pub fn lookup_extern(&self, def_id: &DefId) -> Option<&DefId> {
        self.extern_specs.get(def_id)
    }
}
