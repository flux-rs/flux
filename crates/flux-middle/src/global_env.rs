use std::{borrow::Borrow, rc::Rc};

use flux_errors::FluxSession;
use rustc_hash::FxHashSet;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    LangItem,
};
use rustc_middle::ty::{TyCtxt, Variance};
pub use rustc_span::{symbol::Ident, Symbol};

use crate::{
    cstore::CrateStoreDyn,
    fhir::{self, FluxLocalDefId, VariantIdx},
    intern::List,
    queries::{Providers, Queries, QueryErr, QueryResult},
    rty::{self, fold::TypeFoldable, normalize::Defns, refining::Refiner},
    rustc::{self, lowering, ty},
};

pub struct GlobalEnv<'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'sess FluxSession,
    cstore: Box<CrateStoreDyn>,
    map: fhir::Map,
    queries: Queries<'tcx>,
}

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'sess FluxSession, cstore: Box<CrateStoreDyn>) -> Self {
        GlobalEnv { tcx, sess, cstore, map: fhir::Map::new(), queries: Queries::default() }
    }

    pub fn providers(&mut self) -> &mut Providers {
        &mut self.queries.providers
    }

    pub fn map(&self) -> &fhir::Map {
        &self.map
    }

    pub fn map_mut(&mut self) -> &mut fhir::Map {
        &mut self.map
    }

    pub fn defns(&self) -> QueryResult<&Defns> {
        self.queries.defns(self)
    }

    pub fn qualifiers(
        &self,
        did: LocalDefId,
    ) -> QueryResult<impl Iterator<Item = &rty::Qualifier>> {
        let names: FxHashSet<Symbol> = self.map().get_fn_quals(did).map(|qual| qual.name).collect();
        Ok(self
            .queries
            .qualifiers(self)?
            .iter()
            .filter(move |qualifier| qualifier.global || names.contains(&qualifier.name)))
    }

    pub fn func_decls(&self) -> impl Iterator<Item = &rty::FuncDecl> {
        self.queries.func_decls(self).values()
    }

    pub fn func_decl(&self, name: impl Borrow<Symbol>) -> &rty::FuncDecl {
        &self.queries.func_decls(self)[name.borrow()]
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn mk_box(&self, ty: rty::Ty, alloc: rty::Ty) -> rty::Ty {
        let def_id = self.tcx.require_lang_item(LangItem::OwnedBox, None);
        let adt_def = self.adt_def(def_id).unwrap();

        let args = vec![rty::GenericArg::Ty(ty), rty::GenericArg::Ty(alloc)];

        let bty = rty::BaseTy::adt(adt_def, args);
        rty::Ty::indexed(bty, rty::Expr::unit_adt(def_id))
    }

    pub fn mir(&self, def_id: LocalDefId) -> QueryResult<Rc<rustc::mir::Body<'tcx>>> {
        self.queries.mir(self, def_id)
    }

    pub fn lower_generics_of(&self, def_id: impl Into<DefId>) -> QueryResult<ty::Generics<'tcx>> {
        self.queries.lower_generics_of(self, def_id.into())
    }

    pub fn lower_predicates_of(
        &self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<ty::GenericPredicates> {
        self.queries.lower_predicates_of(self, def_id.into())
    }

    pub fn lower_type_of(&self, def_id: impl Into<DefId>) -> QueryResult<ty::EarlyBinder<ty::Ty>> {
        self.queries.lower_type_of(self, def_id.into())
    }

    pub fn lower_fn_sig(&self, def_id: DefId) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        self.queries.lower_fn_sig(self, def_id)
    }

    pub fn adt_def(&self, def_id: impl Into<DefId>) -> QueryResult<rty::AdtDef> {
        self.queries.adt_def(self, def_id.into())
    }

    pub fn adt_sort_def_of(&self, def_id: impl Into<DefId>) -> rty::AdtSortDef {
        self.queries.adt_sort_def_of(self, def_id.into())
    }

    pub fn check_wf(
        &self,
        flux_id: impl Into<FluxLocalDefId>,
    ) -> QueryResult<Rc<rty::WfckResults>> {
        self.queries.check_wf(self, flux_id.into())
    }

    pub fn impl_trait_ref(
        &self,
        impl_id: DefId,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::TraitRef>>> {
        let Some(poly_trait_ref) = self.tcx.impl_trait_ref(impl_id) else { return Ok(None) };

        let impl_generics = self.generics_of(impl_id)?;
        let trait_ref = poly_trait_ref.skip_binder();
        let args = lowering::lower_generic_args(self.tcx, trait_ref.args)
            .map_err(|err| QueryErr::unsupported(self.tcx, impl_id, err.into_err()))?;
        let args = self.refine_default_generic_args(&impl_generics, &args)?;
        let trait_ref = rty::TraitRef { def_id: trait_ref.def_id, args };
        Ok(Some(rty::EarlyBinder(trait_ref)))
    }

    pub fn generics_of(&self, def_id: impl Into<DefId>) -> QueryResult<rty::Generics> {
        self.queries.generics_of(self, def_id.into())
    }

    pub fn refinement_generics_of(
        &self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::RefinementGenerics> {
        self.queries.refinement_generics_of(self, def_id.into())
    }

    pub fn predicates_of(
        &self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        self.queries.predicates_of(self, def_id.into())
    }

    pub fn assoc_predicates_of(&self, def_id: impl Into<DefId>) -> rty::AssocPredicates {
        self.queries.assoc_predicates_of(self, def_id.into())
    }

    pub fn assoc_predicate_def(
        &self,
        impl_id: DefId,
        name: Symbol,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        self.queries.assoc_predicate_def(self, impl_id, name)
    }

    pub fn sort_of_assoc_pred(
        &self,
        def_id: impl Into<DefId>,
        name: Symbol,
    ) -> rty::EarlyBinder<rty::FuncSort> {
        self.queries.sort_of_assoc_pred(self, def_id.into(), name)
    }

    pub fn item_bounds(&self, def_id: DefId) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
        self.queries.item_bounds(self, def_id)
    }

    pub fn type_of(&self, def_id: DefId) -> QueryResult<rty::EarlyBinder<rty::PolyTy>> {
        self.queries.type_of(self, def_id)
    }

    pub fn fn_sig(
        &self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        self.queries.fn_sig(self, def_id.into())
    }

    pub fn variants_of(
        &self,
        def_id: DefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        self.queries.variants_of(self, def_id)
    }

    pub fn variant_sig(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariant>>> {
        Ok(self
            .variants_of(def_id)?
            .map(|variants| variants.map(|variants| variants[variant_idx.as_usize()].clone())))
    }

    pub fn lower_late_bound_vars(
        &self,
        def_id: LocalDefId,
    ) -> QueryResult<List<rustc::ty::BoundVariableKind>> {
        self.queries.lower_late_bound_vars(self, def_id)
    }

    pub fn get_generic_param(&self, def_id: LocalDefId) -> &fhir::GenericParam {
        let owner = self.hir().ty_param_owner(def_id);
        self.map()
            .get_generics(self.tcx, owner)
            .unwrap()
            .get_param(def_id)
    }

    pub fn is_box(&self, res: fhir::Res) -> bool {
        res.is_box(self.tcx)
    }

    pub fn def_id_to_param_ty(&self, def_id: LocalDefId) -> rty::ParamTy {
        rty::ParamTy {
            index: self.def_id_to_param_index(def_id),
            name: self.tcx.hir().ty_param_name(def_id),
        }
    }

    pub fn def_id_to_param_index(&self, def_id: LocalDefId) -> u32 {
        let item_def_id = self.tcx.hir().ty_param_owner(def_id);
        let generics = self.tcx.generics_of(item_def_id);
        generics.param_def_id_to_index[&def_id.to_def_id()]
    }

    /// Whether values of this sort can be compared for equality.
    pub fn has_equality(&self, sort: &rty::Sort) -> bool {
        match sort {
            rty::Sort::Int
            | rty::Sort::Bool
            | rty::Sort::Real
            | rty::Sort::BitVec(_)
            | rty::Sort::Param(_)
            | rty::Sort::Var(_) => true,
            rty::Sort::Tuple(sorts) => sorts.iter().all(|sort| self.has_equality(sort)),
            rty::Sort::Adt(sort_def, sort_args) => {
                sort_def
                    .sorts(sort_args)
                    .iter()
                    .all(|sort| self.has_equality(sort))
            }
            rty::Sort::App(ctor, sorts) => self.ctor_has_equality(ctor, sorts),
            rty::Sort::Err | rty::Sort::Loc | rty::Sort::Func(_) | rty::Sort::Infer(_) => false,
        }
    }

    /// For now all sort constructors have equality if all the generic arguments do. In the
    /// future we may have a more fine-grained notion of equality for sort constructors.
    fn ctor_has_equality(&self, _: &rty::SortCtor, args: &[rty::Sort]) -> bool {
        args.iter().all(|sort| self.has_equality(sort))
    }

    pub fn refine_default_generic_args(
        &self,
        generics: &rty::Generics,
        args: &ty::GenericArgs,
    ) -> QueryResult<rty::GenericArgs> {
        let refiner = Refiner::default(self, generics);
        let mut res = vec![];
        for arg in args {
            res.push(refiner.refine_generic_arg_raw(arg)?);
        }
        Ok(res.into())
    }

    pub fn refine_default(
        &self,
        generics: &rty::Generics,
        rustc_ty: &ty::Ty,
    ) -> QueryResult<rty::Ty> {
        Refiner::default(self, generics).refine_ty(rustc_ty)
    }

    pub fn refine_with_holes(
        &self,
        generics: &rty::Generics,
        rustc_ty: &ty::Ty,
    ) -> QueryResult<rty::Ty> {
        Refiner::with_holes(self, generics).refine_ty(rustc_ty)
    }

    pub fn instantiate_arg_for_fun(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        Refiner::new(self, generics, |bty| {
            let sort = bty.sort();
            let mut ty = rty::Ty::indexed(bty.shift_in_escaping(1), rty::Expr::nu());
            if !sort.is_unit() {
                ty = rty::Ty::constr(rty::Expr::hole(rty::HoleKind::Pred), ty);
            }
            rty::Binder::with_sort(ty, sort)
        })
        .refine_generic_arg(param, arg)
    }

    pub fn instantiate_arg_for_constructor(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        Refiner::with_holes(self, generics).refine_generic_arg(param, arg)
    }

    pub(crate) fn cstore(&self) -> &CrateStoreDyn {
        &*self.cstore
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }

    pub(crate) fn lookup_extern(&self, def_id: DefId) -> Option<DefId> {
        self.map().get_extern(def_id).map(LocalDefId::to_def_id)
    }

    pub(crate) fn is_fn_once_output(&self, def_id: DefId) -> bool {
        self.tcx
            .require_lang_item(rustc_hir::LangItem::FnOnceOutput, None)
            == def_id
    }
}
