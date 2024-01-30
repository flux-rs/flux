use std::{alloc, ptr, rc::Rc, slice};

use flux_common::bug;
use flux_errors::FluxSession;
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
    rty::{self, normalize::Defns, refining::Refiner},
    rustc::{self, lowering, ty},
};

#[derive(Clone, Copy)]
pub struct GlobalEnv<'genv, 'tcx> {
    inner: &'genv GlobalEnvInner<'genv, 'tcx>,
}

struct GlobalEnvInner<'genv, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'genv FluxSession,
    arena: &'genv fhir::Arena,
    cstore: Box<CrateStoreDyn>,
    queries: Queries<'genv, 'tcx>,
}

impl<'tcx> GlobalEnv<'_, 'tcx> {
    pub fn enter<'a, R>(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        cstore: Box<CrateStoreDyn>,
        arena: &'a fhir::Arena,
        providers: Providers,
        f: impl for<'genv> FnOnce(GlobalEnv<'genv, 'tcx>) -> R,
    ) -> R {
        let inner = GlobalEnvInner { tcx, sess, cstore, arena, queries: Queries::new(providers) };
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

    pub fn collect_specs(self) -> &'genv crate::Specs {
        self.inner.queries.collect_specs(self)
    }

    pub fn fhir_crate(self) -> &'genv fhir::Crate<'genv> {
        self.inner.queries.fhir_crate(self)
    }

    pub fn map(self) -> Map<'genv, 'tcx> {
        Map::new(self, self.fhir_crate())
    }

    pub fn alloc<T>(&self, val: T) -> &'genv T {
        self.inner.arena.alloc(val)
    }

    pub fn alloc_slice<T: Copy>(self, slice: &[T]) -> &'genv [T] {
        self.inner.arena.alloc_slice_copy(slice)
    }

    pub fn alloc_slice_fill_iter<T, I>(self, it: I) -> &'genv [T]
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        self.inner.arena.alloc_slice_fill_iter(it)
    }

    pub fn def_kind(&self, def_id: impl Into<DefId>) -> DefKind {
        self.tcx().def_kind(def_id.into())
    }

    /// Allocates space to store `cap` elements of type `T`.
    ///
    /// The elements are initialized using the supplied iterator. At most `cap` elements will be
    /// retrived from the iterator. If the iterator yields fewer than `cap` elements, the returned
    /// slice will be of length less than the allocated capacity.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice fails.
    pub fn alloc_slice_with_capacity<T, I>(self, cap: usize, it: I) -> &'genv [T]
    where
        I: IntoIterator<Item = T>,
    {
        let layout = alloc::Layout::array::<T>(cap).unwrap_or_else(|_| panic!("out of memory"));
        let dst = self.inner.arena.alloc_layout(layout).cast::<T>();
        unsafe {
            let mut len = 0;
            for (i, v) in it.into_iter().take(cap).enumerate() {
                len += 1;
                ptr::write(dst.as_ptr().add(i), v);
            }

            slice::from_raw_parts(dst.as_ptr(), len)
        }
    }

    pub fn defns(&self) -> QueryResult<&Defns> {
        self.inner.queries.defns(*self)
    }

    pub fn qualifiers(
        self,
        did: LocalDefId,
    ) -> QueryResult<impl Iterator<Item = &'genv rty::Qualifier>> {
        let names: FxHashSet<Symbol> = self
            .map()
            .fn_quals_for(did)
            .iter()
            .map(|qual| qual.name)
            .collect();
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
    ) -> Option<rty::EarlyBinder<rty::FuncSort>> {
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
    fhir: &'genv fhir::Crate<'genv>,
}

impl<'genv, 'tcx> Map<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, fhir: &'genv fhir::Crate<'genv>) -> Self {
        Self { genv, fhir }
    }

    pub fn get_generics(self, def_id: LocalDefId) -> Option<&'genv fhir::Generics<'genv>> {
        match self.genv.def_kind(def_id) {
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

    pub fn get_local_id_for_extern(self, extern_def_id: DefId) -> Option<LocalDefId> {
        self.fhir.externs.get(&extern_def_id).copied()
    }

    pub fn get_flux_item(self, name: Symbol) -> Option<&'genv fhir::FluxItem<'genv>> {
        self.fhir.flux_items.get(&name).as_ref().copied()
    }

    pub fn refined_by(self, def_id: LocalDefId) -> &'genv fhir::RefinedBy<'genv> {
        match self.genv.def_kind(def_id) {
            DefKind::Struct => self.expect_struct(def_id).refined_by,
            DefKind::Enum => self.expect_enum(def_id).refined_by,
            DefKind::TyAlias => self.expect_type_alias(def_id).refined_by,
            _ => bug!("expected struct, enum or type alias"),
        }
    }

    pub fn extern_id_of(self, def_id: LocalDefId) -> Option<DefId> {
        match self.genv.def_kind(def_id) {
            DefKind::Struct => self.expect_struct(def_id).extern_id,
            DefKind::Enum => self.expect_enum(def_id).extern_id,
            _ => None,
        }
    }

    pub fn func_decls(self) -> impl Iterator<Item = &'genv fhir::FuncDecl<'genv>> {
        self.fhir.func_decls.values()
    }

    pub fn defns(self) -> impl Iterator<Item = &'genv fhir::Defn<'genv>> {
        self.fhir.flux_items.values().filter_map(|item| {
            if let fhir::FluxItem::Defn(defn) = item {
                Some(defn)
            } else {
                None
            }
        })
    }

    pub fn defn(&self, name: Symbol) -> Option<&'genv fhir::Defn<'genv>> {
        self.fhir.flux_items.get(&name).and_then(|item| {
            if let fhir::FluxItem::Defn(defn) = item {
                Some(defn)
            } else {
                None
            }
        })
    }

    pub fn qualifiers(self) -> impl Iterator<Item = &'genv fhir::Qualifier<'genv>> {
        self.fhir.flux_items.values().filter_map(|item| {
            if let fhir::FluxItem::Qualifier(qual) = item {
                Some(qual)
            } else {
                None
            }
        })
    }

    pub fn fn_quals_for(self, def_id: LocalDefId) -> &'genv [fhir::SurfaceIdent] {
        self.fhir.fn_quals.get(&def_id).copied().unwrap_or(&[])
    }

    pub fn consts(self) -> impl Iterator<Item = fhir::ConstInfo> + 'genv {
        self.fhir.consts.values().copied()
    }

    pub fn is_trusted(self, def_id: LocalDefId) -> bool {
        self.fhir.trusted.contains(&def_id)
    }

    pub fn expect_enum(self, def_id: LocalDefId) -> &'genv fhir::EnumDef<'genv> {
        if let fhir::ItemKind::Enum(enum_def) = &self.fhir.items[&def_id].kind {
            enum_def
        } else {
            bug!("expected `fhir::ItemKind:Enum`")
        }
    }

    pub fn expect_struct(self, def_id: LocalDefId) -> &'genv fhir::StructDef<'genv> {
        if let fhir::ItemKind::Struct(struct_def) = &self.fhir.items[&def_id].kind {
            struct_def
        } else {
            bug!("expected `fhir::ItemKind::Struct`")
        }
    }

    pub fn expect_impl(self, def_id: LocalDefId) -> &'genv fhir::Impl<'genv> {
        if let fhir::ItemKind::Impl(impl_) = &self.fhir.items[&def_id].kind {
            impl_
        } else {
            bug!("expected `fhir::ItemKind::Impl`")
        }
    }

    pub fn expect_trait(self, def_id: LocalDefId) -> &'genv fhir::Trait<'genv> {
        if let fhir::ItemKind::Trait(trait_) = &self.fhir.items[&def_id].kind {
            trait_
        } else {
            bug!("expected `fhir::ItemKind::Trait`")
        }
    }

    pub fn expect_opaque_ty(self, def_id: LocalDefId) -> &'genv fhir::OpaqueTy<'genv> {
        if let fhir::ItemKind::OpaqueTy(opaque_ty) = &self.fhir.items[&def_id].kind {
            opaque_ty
        } else {
            bug!("expected `fhir::ItemKind::OpaqueTy`")
        }
    }

    pub fn expect_fn_like(self, def_id: LocalDefId) -> &'genv fhir::FnSig<'genv> {
        if let Some(item) = self.fhir.items.get(&def_id)
            && let fhir::ItemKind::Fn(fn_sig) = &item.kind
        {
            fn_sig
        } else if let Some(trait_item) = self.fhir.trait_items.get(&def_id)
            && let fhir::TraitItemKind::Fn(fn_sig) = &trait_item.kind
        {
            fn_sig
        } else if let Some(impl_item) = self.fhir.impl_items.get(&def_id) {
            let fhir::ImplItemKind::Fn(fn_sig) = &impl_item.kind;
            fn_sig
        } else {
            bug!("expected `fhir::ItemKind::Fn`, `fhir::TraitItemKind::Fn` or `fhir::ImpItemKind::Fn`");
        }
    }

    pub fn expect_type_alias(self, def_id: LocalDefId) -> &'genv fhir::TyAlias<'genv> {
        if let fhir::ItemKind::TyAlias(ty_alias) = &self.fhir.items[&def_id].kind {
            ty_alias
        } else {
            bug!("expected `fhir::ItemKind::TyAlias`")
        }
    }

    pub fn expect_assoc_type(self, def_id: LocalDefId) -> &'genv fhir::AssocType<'genv> {
        if let fhir::TraitItemKind::Type(assoc_type) = &self.fhir.trait_items[&def_id].kind {
            assoc_type
        } else {
            bug!("expected `fhir::TraitItemKind::Type`")
        }
    }
}

#[macro_export]
macro_rules! try_alloc_slice {
    ($genv:expr, $slice:expr, $map:expr $(,)?) => {{
        let slice = $slice;
        $crate::try_alloc_slice!($genv, cap: slice.len(), slice.into_iter().map($map))
    }};
    ($genv:expr, cap: $cap:expr, $it:expr $(,)?) => {{
        let mut err = None;
        let slice = $genv.alloc_slice_with_capacity($cap, $it.into_iter().collect_errors(&mut err));
        err.map_or(Ok(slice), Err)
    }};
}
