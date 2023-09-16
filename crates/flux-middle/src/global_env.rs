use std::{borrow::Borrow, rc::Rc};

use flux_common::bug;
use flux_errors::FluxSession;
use rustc_hash::FxHashSet;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    LangItem, PrimTy,
};
use rustc_middle::ty::{TyCtxt, Variance};
pub use rustc_span::{symbol::Ident, Symbol};

use crate::{
    cstore::CrateStoreDyn,
    fhir::{self, FluxLocalDefId, VariantIdx},
    intern::List,
    queries::{Providers, Queries, QueryResult},
    rty::{self, fold::TypeFoldable, normalize::Defns, refining::Refiner},
    rustc::{self, ty},
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

    pub fn lower_type_of(&self, def_id: impl Into<DefId>) -> QueryResult<ty::EarlyBinder<ty::Ty>> {
        self.queries.lower_type_of(self, def_id.into())
    }

    pub fn lower_fn_sig(&self, def_id: DefId) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
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

    pub fn refine_params_of(
        &self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<List<rty::RefineParam>> {
        Ok(self.generics_of(def_id)?.refine_params.clone())
    }

    pub fn generics_of(&self, def_id: impl Into<DefId>) -> QueryResult<rty::Generics> {
        self.queries.generics_of(self, def_id.into())
    }

    pub fn predicates_of(
        &self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        self.queries.predicates_of(self, def_id.into())
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
        self.map().get_generics(owner).unwrap().get_param(def_id)
    }

    pub fn is_box(&self, res: fhir::Res) -> bool {
        if let fhir::Res::Def(DefKind::Struct, def_id) = res {
            self.tcx.adt_def(def_id).is_box()
        } else {
            false
        }
    }

    pub fn func_decl(&self, name: impl Borrow<Symbol>) -> Option<&fhir::FuncDecl> {
        self.map().func_decl(name)
    }

    pub fn const_by_name(&self, name: impl Borrow<Symbol>) -> Option<&fhir::ConstInfo> {
        self.map().const_by_name(name)
    }

    pub fn sort_of_bty(&self, bty: &fhir::BaseTy) -> Option<fhir::Sort> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(_, fhir::Path { res, .. })) => {
                self.sort_of_res(*res)
            }
            fhir::BaseTyKind::Slice(_) => Some(fhir::Sort::Int),
        }
    }

    pub fn index_sorts_of(&self, def_id: impl Into<DefId>) -> &[fhir::Sort] {
        let def_id = def_id.into();
        if let Some(local_id) = def_id.as_local().or_else(|| self.map().get_extern(def_id)) {
            self.map().refined_by(local_id).index_sorts()
        } else {
            self.cstore()
                .refined_by(def_id)
                .map(fhir::RefinedBy::index_sorts)
                .unwrap_or_default()
        }
    }

    pub fn sort_of_res(&self, res: fhir::Res) -> Option<fhir::Sort> {
        let sort = match res {
            fhir::Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_)) => fhir::Sort::Int,
            fhir::Res::PrimTy(PrimTy::Bool) => fhir::Sort::Bool,
            fhir::Res::PrimTy(PrimTy::Float(..) | PrimTy::Str | PrimTy::Char) => fhir::Sort::Unit,
            fhir::Res::Def(DefKind::TyAlias { .. } | DefKind::Enum | DefKind::Struct, def_id) => {
                fhir::Sort::Record(def_id)
            }
            fhir::Res::SelfTyAlias { alias_to, .. } => {
                let self_ty = self.tcx.type_of(alias_to).skip_binder();
                if let rustc_type_ir::TyKind::Adt(adt_def, _) = self_ty.kind() {
                    fhir::Sort::Record(adt_def.did())
                } else {
                    bug!("unexpected res {res:?}")
                }
            }
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                let param = self.get_generic_param(def_id.expect_local());
                match &param.kind {
                    fhir::GenericParamKind::BaseTy => fhir::Sort::Param(def_id),
                    fhir::GenericParamKind::Type { .. } | fhir::GenericParamKind::Lifetime => {
                        return None
                    }
                }
            }
            fhir::Res::Def(DefKind::AssocTy | DefKind::OpaqueTy, _)
            | fhir::Res::SelfTyParam { .. } => return None,
            fhir::Res::Def(..) => bug!("unexpected res {res:?}"),
        };
        Some(sort)
    }

    pub fn early_bound_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        if let Some(local_id) = def_id.as_local() {
            self.map().refined_by(local_id).early_bound_sorts()
        } else {
            self.cstore()
                .refined_by(def_id)
                .map(fhir::RefinedBy::early_bound_sorts)
                .unwrap_or_default()
        }
    }

    /// Whether values of this sort can be compared for equality.
    pub fn has_equality(&self, sort: &fhir::Sort) -> bool {
        match sort {
            fhir::Sort::Int
            | fhir::Sort::Bool
            | fhir::Sort::Real
            | fhir::Sort::Unit
            | fhir::Sort::BitVec(_) => true,
            fhir::Sort::Record(def_id) => {
                self.index_sorts_of(*def_id)
                    .iter()
                    .all(|sort| self.has_equality(sort))
            }
            fhir::Sort::App(ctor, sorts) => self.ctor_has_equality(ctor, sorts),
            fhir::Sort::Loc
            | fhir::Sort::Func(_)
            | fhir::Sort::Param(_)
            | fhir::Sort::Wildcard
            | fhir::Sort::Infer(_) => false,
        }
    }

    /// For now all sort constructors have equality if all the generic arguments do. In the
    /// future we may have a more fine-grained notion of equality for sort constructors.
    fn ctor_has_equality(&self, _: &fhir::SortCtor, args: &[fhir::Sort]) -> bool {
        args.iter().all(|sort| self.has_equality(sort))
    }

    pub fn field_sort(&self, def_id: DefId, fld: Symbol) -> Option<&fhir::Sort> {
        if let Some(local_id) = def_id.as_local() {
            self.map().refined_by(local_id).field_sort(fld)
        } else {
            self.cstore()
                .refined_by(def_id)
                .and_then(|refined_by| refined_by.field_sort(fld))
        }
    }

    pub fn field_index(&self, def_id: DefId, fld: Symbol) -> Option<usize> {
        if let Some(local_id) = def_id.as_local() {
            self.map().refined_by(local_id).field_index(fld)
        } else {
            self.cstore()
                .refined_by(def_id)
                .and_then(|refined_by| refined_by.field_index(fld))
        }
    }

    pub fn refine_default_generic_args(
        &self,
        generics: &rty::Generics,
        args: &ty::GenericArgs,
    ) -> QueryResult<rty::GenericArgs> {
        let refiner = Refiner::default(self, generics);
        let mut res = vec![];
        for arg in args.iter() {
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
