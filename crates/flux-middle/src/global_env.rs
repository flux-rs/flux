use std::{
    borrow::Borrow,
    cell::{self, RefCell, RefMut},
    rc::Rc,
};

use flux_errors::FluxSession;
use rustc_data_structures::unord::{ExtendUnord as _, UnordMap};
use rustc_hash::FxHashSet;
use rustc_hir::{
    def::DefKind,
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

#[derive(Clone, Copy)]
pub struct GlobalEnv<'genv, 'tcx> {
    inner: &'genv GlobalEnvInner<'genv, 'tcx>,
}

type Arena = bumpalo::Bump;

struct GlobalEnvInner<'genv, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'genv FluxSession,
    fhir: RefCell<fhir::Crate<'genv>>,
    arena: &'genv Arena,
    cstore: Box<CrateStoreDyn>,
    queries: Queries<'genv, 'tcx>,
}

impl<'tcx> GlobalEnv<'_, 'tcx> {
    pub fn enter<'a, R>(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        cstore: Box<CrateStoreDyn>,
        arena: &'a Arena,
        providers: Providers,
        f: impl for<'genv> FnOnce(GlobalEnv<'genv, 'tcx>) -> R,
    ) -> R {
        let map = RefCell::new(fhir::Crate::default());
        let inner = GlobalEnvInner {
            tcx,
            sess,
            cstore,
            arena,
            fhir: map,
            queries: Queries::new(providers),
        };
        f(GlobalEnv { inner: &inner })
    }
}

impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    pub fn tcx(self) -> TyCtxt<'tcx> {
        self.inner.tcx
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx().hir()
    }

    pub fn sess(self) -> &'genv FluxSession {
        self.inner.sess
    }

    pub fn map(self) -> Map<'genv, 'tcx> {
        Map { genv: self }
    }

    pub fn borrow_map_mut(self) -> Map<'genv, 'tcx> {
        Map { genv: self }
    }

    pub fn alloc<T>(&self, val: T) -> &'genv T {
        self.inner.arena.alloc(val)
    }

    pub fn alloc_slice<T: Copy>(&self, slice: &[T]) -> &'genv [T] {
        self.inner.arena.alloc_slice_copy(slice)
    }

    pub fn alloc_slice_fill_iter<T, I>(&self, it: I) -> &'genv [T]
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        self.inner.arena.alloc_slice_fill_iter(it)
    }

    pub fn defns(&self) -> QueryResult<&Defns> {
        self.inner.queries.defns(*self)
    }

    pub fn qualifiers(
        self,
        did: LocalDefId,
    ) -> QueryResult<impl Iterator<Item = &'genv rty::Qualifier>> {
        let names: FxHashSet<Symbol> = self.map().get_fn_quals(did).map(|qual| qual.name).collect();
        Ok(self
            .inner
            .queries
            .qualifiers(self)?
            .iter()
            .filter(move |qualifier| qualifier.global || names.contains(&qualifier.name)))
    }

    pub fn func_decls(self) -> impl Iterator<Item = &'genv rty::FuncDecl> {
        self.inner.queries.func_decls(self).values()
    }

    pub fn func_decl(self, name: Symbol) -> rty::FuncDecl {
        self.inner.queries.func_decls(self)[&name].clone()
    }

    pub fn variances_of(self, did: DefId) -> &'tcx [Variance] {
        self.tcx().variances_of(did)
    }

    pub fn mk_box(&self, ty: rty::Ty, alloc: rty::Ty) -> rty::Ty {
        let def_id = self.tcx().require_lang_item(LangItem::OwnedBox, None);
        let adt_def = self.adt_def(def_id).unwrap();

        let args = vec![rty::GenericArg::Ty(ty), rty::GenericArg::Ty(alloc)];

        let bty = rty::BaseTy::adt(adt_def, args);
        rty::Ty::indexed(bty, rty::Expr::unit_adt(def_id))
    }

    pub fn mir(self, def_id: LocalDefId) -> QueryResult<Rc<rustc::mir::Body<'tcx>>> {
        self.inner.queries.mir(self, def_id)
    }

    pub fn lower_generics_of(self, def_id: impl Into<DefId>) -> QueryResult<ty::Generics<'tcx>> {
        self.inner.queries.lower_generics_of(self, def_id.into())
    }

    pub fn lower_predicates_of(
        self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<ty::GenericPredicates> {
        self.inner.queries.lower_predicates_of(self, def_id.into())
    }

    pub fn lower_type_of(self, def_id: impl Into<DefId>) -> QueryResult<ty::EarlyBinder<ty::Ty>> {
        self.inner.queries.lower_type_of(self, def_id.into())
    }

    pub fn lower_fn_sig(self, def_id: DefId) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        self.inner.queries.lower_fn_sig(self, def_id)
    }

    pub fn adt_def(self, def_id: impl Into<DefId>) -> QueryResult<rty::AdtDef> {
        self.inner.queries.adt_def(self, def_id.into())
    }

    pub fn adt_sort_def_of(self, def_id: impl Into<DefId>) -> rty::AdtSortDef {
        self.inner.queries.adt_sort_def_of(self, def_id.into())
    }

    pub fn check_wf(
        self,
        flux_id: impl Into<FluxLocalDefId>,
    ) -> QueryResult<Rc<rty::WfckResults<'genv>>> {
        self.inner.queries.check_wf(self, flux_id.into())
    }

    pub fn impl_trait_ref(
        self,
        impl_id: DefId,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::TraitRef>>> {
        let Some(poly_trait_ref) = self.tcx().impl_trait_ref(impl_id) else { return Ok(None) };

        let impl_generics = self.generics_of(impl_id)?;
        let trait_ref = poly_trait_ref.skip_binder();
        let args = lowering::lower_generic_args(self.tcx(), trait_ref.args)
            .map_err(|err| QueryErr::unsupported(self.tcx(), impl_id, err.into_err()))?;
        let args = self.refine_default_generic_args(&impl_generics, &args)?;
        let trait_ref = rty::TraitRef { def_id: trait_ref.def_id, args };
        Ok(Some(rty::EarlyBinder(trait_ref)))
    }

    pub fn generics_of(self, def_id: impl Into<DefId>) -> QueryResult<rty::Generics> {
        self.inner.queries.generics_of(self, def_id.into())
    }

    pub fn refinement_generics_of(
        self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::RefinementGenerics> {
        self.inner
            .queries
            .refinement_generics_of(self, def_id.into())
    }

    pub fn predicates_of(
        self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        self.inner.queries.predicates_of(self, def_id.into())
    }

    pub fn assoc_predicates_of(self, def_id: impl Into<DefId>) -> rty::AssocPredicates {
        self.inner.queries.assoc_predicates_of(self, def_id.into())
    }

    pub fn assoc_predicate_def(
        self,
        impl_id: DefId,
        name: Symbol,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        self.inner.queries.assoc_predicate_def(self, impl_id, name)
    }

    pub fn sort_of_assoc_pred(
        self,
        def_id: impl Into<DefId>,
        name: Symbol,
    ) -> rty::EarlyBinder<rty::FuncSort> {
        self.inner
            .queries
            .sort_of_assoc_pred(self, def_id.into(), name)
    }

    pub fn item_bounds(self, def_id: DefId) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
        self.inner.queries.item_bounds(self, def_id)
    }

    pub fn type_of(self, def_id: DefId) -> QueryResult<rty::EarlyBinder<rty::PolyTy>> {
        self.inner.queries.type_of(self, def_id)
    }

    pub fn fn_sig(self, def_id: impl Into<DefId>) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        self.inner.queries.fn_sig(self, def_id.into())
    }

    pub fn variants_of(
        self,
        def_id: DefId,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        self.inner.queries.variants_of(self, def_id)
    }

    pub fn variant_sig(
        self,
        def_id: DefId,
        variant_idx: VariantIdx,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariant>>> {
        Ok(self
            .variants_of(def_id)?
            .map(|variants| variants.map(|variants| variants[variant_idx.as_usize()].clone())))
    }

    pub fn lower_late_bound_vars(
        self,
        def_id: LocalDefId,
    ) -> QueryResult<List<rustc::ty::BoundVariableKind>> {
        self.inner.queries.lower_late_bound_vars(self, def_id)
    }

    pub fn get_generic_param(&self, def_id: LocalDefId) -> &fhir::GenericParam {
        let owner = self.hir().ty_param_owner(def_id);
        self.map().get_generics(owner).unwrap().get_param(def_id)
    }

    pub fn is_box(&self, res: fhir::Res) -> bool {
        res.is_box(self.tcx())
    }

    pub fn def_id_to_param_ty(&self, def_id: LocalDefId) -> rty::ParamTy {
        rty::ParamTy {
            index: self.def_id_to_param_index(def_id),
            name: self.tcx().hir().ty_param_name(def_id),
        }
    }

    pub fn def_id_to_param_index(&self, def_id: LocalDefId) -> u32 {
        let item_def_id = self.hir().ty_param_owner(def_id);
        let generics = self.tcx().generics_of(item_def_id);
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
        self,
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
        self,
        generics: &rty::Generics,
        rustc_ty: &ty::Ty,
    ) -> QueryResult<rty::Ty> {
        Refiner::default(self, generics).refine_ty(rustc_ty)
    }

    pub fn refine_with_holes(
        self,
        generics: &rty::Generics,
        rustc_ty: &ty::Ty,
    ) -> QueryResult<rty::Ty> {
        Refiner::with_holes(self, generics).refine_ty(rustc_ty)
    }

    pub fn instantiate_arg_for_fun(
        self,
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
        self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        Refiner::with_holes(self, generics).refine_generic_arg(param, arg)
    }

    pub(crate) fn cstore(self) -> &'genv CrateStoreDyn {
        &*self.inner.cstore
    }

    pub(crate) fn lookup_extern(&self, def_id: DefId) -> Option<DefId> {
        self.map()
            .get_local_id_for_extern(def_id)
            .map(LocalDefId::to_def_id)
    }

    pub(crate) fn is_fn_once_output(&self, def_id: DefId) -> bool {
        self.tcx()
            .require_lang_item(rustc_hir::LangItem::FnOnceOutput, None)
            == def_id
    }
}

#[derive(Clone, Copy)]
pub struct Map<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
}

impl<'genv, 'tcx> Map<'genv, 'tcx> {
    pub fn insert_assoc_type(self, def_id: LocalDefId, assoc_ty: fhir::AssocType<'genv>) {
        self.borrow_mut()
            .assoc_types
            .insert(def_id, self.genv.alloc(assoc_ty));
    }

    pub fn insert_struct(&self, def_id: LocalDefId, struct_def: fhir::StructDef<'genv>) {
        self.borrow_mut()
            .structs
            .insert(def_id, self.genv.alloc(struct_def));
    }

    pub fn insert_enum(&self, def_id: LocalDefId, enum_def: fhir::EnumDef<'genv>) {
        self.borrow_mut()
            .enums
            .insert(def_id, self.genv.alloc(enum_def));
    }

    pub fn insert_type_alias(&self, def_id: LocalDefId, ty_alias: fhir::TyAlias<'genv>) {
        self.borrow_mut()
            .type_aliases
            .insert(def_id, self.genv.alloc(ty_alias));
    }

    pub fn insert_fn_sig(&self, def_id: LocalDefId, fn_sig: fhir::FnSig<'genv>) {
        self.borrow_mut()
            .fns
            .insert(def_id, self.genv.alloc(fn_sig));
    }

    pub fn insert_opaque_tys(
        &self,
        opaque_tys: UnordMap<LocalDefId, &'genv fhir::OpaqueTy<'genv>>,
    ) {
        self.borrow_mut()
            .opaque_tys
            .extend_unord(opaque_tys.into_items());
    }

    pub fn insert_trait(&self, def_id: LocalDefId, trait_: fhir::Trait<'genv>) {
        self.borrow_mut()
            .traits
            .insert(def_id, self.genv.alloc(trait_));
    }

    pub fn insert_impl(&self, def_id: LocalDefId, impl_: fhir::Impl<'genv>) {
        self.borrow_mut()
            .impls
            .insert(def_id, self.genv.alloc(impl_));
    }

    pub fn insert_sort_decl(self, sort_decl: fhir::SortDecl) {
        self.borrow_mut()
            .sort_decls
            .insert(sort_decl.name, sort_decl);
    }

    pub fn insert_const(self, c: fhir::ConstInfo) {
        self.borrow_mut().consts.insert(c.sym, c);
    }

    pub fn insert_func_decl(self, name: Symbol, func_decl: fhir::FuncDecl<'genv>) {
        self.borrow_mut()
            .func_decls
            .insert(name, self.genv.alloc(func_decl));
    }

    pub fn insert_refined_by(self, def_id: LocalDefId, refined_by: fhir::RefinedBy<'genv>) {
        self.borrow_mut()
            .refined_by
            .insert(def_id, self.genv.alloc(refined_by));
    }

    pub fn insert_extern(self, extern_def_id: DefId, local_def_id: LocalDefId) {
        self.borrow_mut()
            .externs
            .insert(extern_def_id, local_def_id);
    }

    pub fn insert_defn(self, name: Symbol, defn: fhir::Defn<'genv>) {
        self.borrow_mut()
            .flux_items
            .insert(name, self.genv.alloc(fhir::FluxItem::Defn(defn)));
    }

    pub fn insert_qualifier(self, qualifier: fhir::Qualifier<'genv>) {
        self.borrow_mut()
            .flux_items
            .insert(qualifier.name, self.genv.alloc(fhir::FluxItem::Qualifier(qualifier)));
    }

    pub fn add_trusted(self, def_id: LocalDefId) {
        self.borrow_mut().trusted.insert(def_id);
    }

    pub fn insert_fn_quals(self, def_id: LocalDefId, quals: Vec<Ident>) {
        self.borrow_mut().fn_quals.insert(def_id, quals);
    }

    fn borrow_mut(self) -> RefMut<'genv, fhir::Crate<'genv>> {
        self.genv.inner.fhir.borrow_mut()
    }

    pub fn get_fn_quals(&self, did: LocalDefId) -> impl Iterator<Item = fhir::SurfaceIdent> {
        [].into_iter()
        // self.borrow()
        //     .fn_quals
        //     .get(&did)
        //     .map_or(&[][..], Vec::as_slice)
        //     .iter()
        //     .copied()
    }

    pub fn get_generics(self, def_id: LocalDefId) -> Option<&'genv fhir::Generics<'genv>> {
        match self.genv.tcx().def_kind(def_id) {
            DefKind::Struct => Some(&self.expect_struct(def_id).generics),
            DefKind::Enum => Some(&self.expect_enum(def_id).generics),
            DefKind::Impl { .. } => Some(&self.expect_impl(def_id).generics),
            DefKind::Trait => Some(&self.expect_trait(def_id).generics),
            DefKind::TyAlias => Some(&self.expect_type_alias(def_id).generics),
            DefKind::AssocTy => Some(&self.expect_assoc_type(def_id).generics),
            DefKind::Fn | DefKind::AssocFn => Some(&self.expect_fn_like(def_id).generics),
            DefKind::OpaqueTy => Some(&self.expect_opaque_ty(def_id).generics),
            _ => None,
        }
    }

    pub fn get_local_id_for_extern(&self, extern_def_id: DefId) -> Option<LocalDefId> {
        self.borrow().externs.get(&extern_def_id).copied()
    }

    pub fn get_flux_item(self, name: Symbol) -> Option<&'genv fhir::FluxItem<'genv>> {
        self.borrow().flux_items.get(&name).copied()
    }

    pub fn func_decl(self, name: Symbol) -> Option<&'genv fhir::FuncDecl<'genv>> {
        self.borrow().func_decls.get(&name).copied()
    }

    pub fn const_by_name(self, name: Symbol) -> Option<fhir::ConstInfo> {
        self.borrow().consts.get(&name).copied()
    }

    pub fn refined_by(self, def_id: LocalDefId) -> &'genv fhir::RefinedBy<'genv> {
        self.borrow().refined_by[&def_id]
    }

    pub fn find_sort(self, name: Symbol) -> Option<fhir::SortDecl> {
        self.borrow().sort_decls.get(&name).copied()
    }

    pub fn extern_id_of(self, def_id: LocalDefId) -> Option<DefId> {
        match self.genv.tcx().def_kind(def_id) {
            DefKind::Struct => self.expect_struct(def_id).extern_id,
            DefKind::Enum => self.expect_enum(def_id).extern_id,
            _ => None,
        }
    }

    pub fn func_decls(self) -> impl Iterator<Item = &'genv fhir::FuncDecl<'genv>> {
        [].into_iter()
    }

    pub fn defns(self) -> impl Iterator<Item = &'genv fhir::Defn<'genv>> {
        [].into_iter()
    }

    pub fn defn(&self, name: Symbol) -> Option<&'genv fhir::Defn<'genv>> {
        self.borrow().flux_items.get(&name).and_then(|item| {
            if let fhir::FluxItem::Defn(defn) = item {
                Some(defn)
            } else {
                None
            }
        })
    }

    pub fn qualifiers(&self) -> impl Iterator<Item = &'genv fhir::Qualifier<'genv>> {
        [].into_iter()
    }

    pub fn fn_quals(&self) -> impl Iterator<Item = (LocalDefId, &'genv [fhir::SurfaceIdent])> {
        [].into_iter()
        // self.fn_quals.iter().map(|(def_id, quals)| (*def_id, quals))
    }

    pub fn consts(&self) -> impl Iterator<Item = fhir::ConstInfo> {
        // self.consts.values().copied()
        [].into_iter()
    }

    pub fn is_trusted(&self, def_id: LocalDefId) -> bool {
        self.borrow().trusted.contains(&def_id)
    }

    pub fn expect_enum(&self, def_id: LocalDefId) -> &'genv fhir::EnumDef<'genv> {
        self.borrow().enums[&def_id]
    }

    pub fn expect_struct(&self, def_id: LocalDefId) -> &'genv fhir::StructDef<'genv> {
        self.borrow().structs[&def_id]
    }

    pub fn expect_impl(&self, def_id: LocalDefId) -> &'genv fhir::Impl<'genv> {
        self.borrow().impls[&def_id]
    }

    pub fn expect_trait(&self, def_id: LocalDefId) -> &'genv fhir::Trait<'genv> {
        self.borrow().traits[&def_id]
    }

    pub fn expect_opaque_ty(&self, def_id: LocalDefId) -> &'genv fhir::OpaqueTy<'genv> {
        self.borrow().opaque_tys[&def_id]
    }

    pub fn expect_fn_like(&self, def_id: LocalDefId) -> &'genv fhir::FnSig<'genv> {
        self.borrow().fns[&def_id]
    }

    pub fn expect_type_alias(&self, def_id: LocalDefId) -> &'genv fhir::TyAlias<'genv> {
        self.borrow().type_aliases[&def_id]
    }

    pub fn expect_assoc_type(&self, def_id: LocalDefId) -> &'genv fhir::AssocType<'genv> {
        self.borrow().assoc_types[&def_id]
    }

    fn borrow(&self) -> cell::Ref<'genv, fhir::Crate<'genv>> {
        self.genv.inner.fhir.borrow()
    }
}
