use std::{alloc, ptr, rc::Rc, slice};

use flux_common::{bug, result::ErrorEmitter};
use flux_config::CrateConfig;
use flux_errors::FluxSession;
use rustc_hash::FxHashSet;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    LangItem,
};
use rustc_middle::ty::{ParamConst, TyCtxt, Variance};
pub use rustc_span::{symbol::Ident, Symbol};

use crate::{
    cstore::CrateStoreDyn,
    fhir::{self, FluxLocalDefId, VariantIdx},
    intern::List,
    queries::{Providers, Queries, QueryErr, QueryResult},
    rty::{self, normalize::SpecFuncDefns, refining::Refiner},
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

    pub fn resolve_crate(self) -> &'genv crate::ResolverOutput {
        self.inner.queries.resolve_crate(self)
    }

    pub fn desugar(self, def_id: LocalDefId) -> QueryResult<fhir::Node<'genv>> {
        self.inner.queries.desugar(self, def_id)
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

    pub fn spec_func_defns(&self) -> QueryResult<&SpecFuncDefns> {
        self.inner.queries.spec_func_defns(*self)
    }

    /// Return all the qualifiers that apply to an item, including both global and local qualifiers.
    pub fn qualifiers_for(
        self,
        did: LocalDefId,
    ) -> QueryResult<impl Iterator<Item = &'genv rty::Qualifier>> {
        let names: FxHashSet<Symbol> = self
            .map()
            .fn_quals_for(did)?
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

    pub fn func_decls(self) -> QueryResult<impl Iterator<Item = &'genv rty::SpecFuncDecl>> {
        Ok(self.inner.queries.func_decls(self)?.values())
    }

    pub fn func_decl(self, name: Symbol) -> QueryResult<rty::SpecFuncDecl> {
        Ok(self.inner.queries.func_decls(self)?[&name].clone())
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

    pub fn lower_fn_sig(
        self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        self.inner.queries.lower_fn_sig(self, def_id.into())
    }

    pub fn adt_def(self, def_id: impl Into<DefId>) -> QueryResult<rty::AdtDef> {
        self.inner.queries.adt_def(self, def_id.into())
    }

    pub fn adt_sort_def_of(self, def_id: impl Into<DefId>) -> QueryResult<rty::AdtSortDef> {
        self.inner.queries.adt_sort_def_of(self, def_id.into())
    }

    pub fn check_wf(self, flux_id: impl Into<FluxLocalDefId>) -> QueryResult<Rc<rty::WfckResults>> {
        self.inner.queries.check_wf(self, flux_id.into())
    }

    pub fn impl_trait_ref(
        self,
        impl_id: DefId,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::TraitRef>>> {
        let impl_id = self.resolve_maybe_extern_id(impl_id);

        let Some(poly_trait_ref) = self.tcx().impl_trait_ref(impl_id) else { return Ok(None) };

        let trait_ref = self.lower_trait_ref(poly_trait_ref.skip_binder())?;
        let impl_generics = self.generics_of(impl_id)?;
        let trait_ref = Refiner::default(self, &impl_generics).refine_trait_ref(&trait_ref)?;
        Ok(Some(rty::EarlyBinder(trait_ref)))
    }

    pub fn lower_trait_ref(
        self,
        trait_ref: rustc_middle::ty::TraitRef<'tcx>,
    ) -> QueryResult<rustc::ty::TraitRef> {
        lowering::lower_trait_ref(self.tcx(), trait_ref)
            .map_err(|err| QueryErr::unsupported(trait_ref.def_id, err.into_err()))
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

    pub fn assoc_refinements_of(
        self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<rty::AssocRefinements> {
        self.inner.queries.assoc_refinements_of(self, def_id.into())
    }

    pub fn assoc_refinement_def(
        self,
        impl_id: DefId,
        name: Symbol,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        self.inner.queries.assoc_refinement_def(self, impl_id, name)
    }

    pub fn sort_of_assoc_reft(
        self,
        def_id: impl Into<DefId>,
        name: Symbol,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>> {
        self.inner
            .queries
            .sort_of_assoc_reft(self, def_id.into(), name)
    }

    pub fn item_bounds(self, def_id: DefId) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
        self.inner.queries.item_bounds(self, def_id)
    }

    pub fn type_of(self, def_id: impl Into<DefId>) -> QueryResult<rty::EarlyBinder<rty::TyCtor>> {
        self.inner.queries.type_of(self, def_id.into())
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

    pub fn get_generic_param(&self, def_id: LocalDefId) -> QueryResult<&fhir::GenericParam> {
        let owner = self.hir().ty_param_owner(def_id);
        Ok(self.map().get_generics(owner)?.unwrap().get_param(def_id))
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

    pub fn def_id_to_param_const(&self, def_id: DefId) -> ParamConst {
        let def_id = def_id.expect_local();
        ParamConst {
            index: self.def_id_to_param_index(def_id),
            name: self.tcx().hir().ty_param_name(def_id),
        }
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

    pub fn is_fn_once_output(&self, def_id: DefId) -> bool {
        self.tcx()
            .require_lang_item(rustc_hir::LangItem::FnOnceOutput, None)
            == def_id
    }

    /// If `def_id` is a local id for an extern spec return the extern id, otherwise return `def_id`.
    pub fn resolve_maybe_extern_id(self, def_id: DefId) -> DefId {
        let Some(local_id) = def_id.as_local() else { return def_id };
        self.collect_specs()
            .local_id_to_extern_id
            .get(&local_id)
            .copied()
            .unwrap_or(def_id)
    }

    pub fn extern_id_of(self, def_id: LocalDefId) -> Option<DefId> {
        self.collect_specs()
            .local_id_to_extern_id
            .get(&def_id)
            .copied()
    }

    pub fn get_local_id_for_extern(self, extern_def_id: DefId) -> Option<LocalDefId> {
        self.collect_specs()
            .extern_id_to_local_id
            .get(&extern_def_id)
            .copied()
    }

    pub fn trusted(self, def_id: LocalDefId) -> bool {
        self.traverse_parents(def_id, |did| self.collect_specs().trusted.get(&did))
            .is_some_and(|trusted| trusted.to_bool())
    }

    /// transitively follows the parent-chain to find the first containing item with an explicit
    /// `ignore` annotation and returns whether that item is ignored or not.
    pub fn ignored(self, def_id: LocalDefId) -> bool {
        self.traverse_parents(def_id, |did| self.collect_specs().ignores.get(&did))
            .is_some_and(|ignored| ignored.to_bool())
    }

    /// traverse the parent chain of a def_id until the first node for which `f` returns [`Some`].
    fn traverse_parents<T>(
        self,
        mut def_id: LocalDefId,
        f: impl Fn(LocalDefId) -> Option<T>,
    ) -> Option<T> {
        loop {
            if let Some(v) = f(def_id) {
                break Some(v);
            }

            if let Some(parent) = self.tcx().opt_local_parent(def_id) {
                def_id = parent;
            } else {
                break None;
            }
        }
    }

    pub fn crate_config(self) -> Option<CrateConfig> {
        self.collect_specs().crate_config
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

    pub fn get_generics(
        self,
        def_id: LocalDefId,
    ) -> QueryResult<Option<&'genv fhir::Generics<'genv>>> {
        // We don't have nodes for closures and coroutines
        if matches!(self.genv.def_kind(def_id), DefKind::Closure) {
            Ok(None)
        } else {
            Ok(Some(self.node(def_id)?.generics()))
        }
    }

    pub fn get_flux_item(self, name: Symbol) -> Option<&'genv fhir::FluxItem<'genv>> {
        self.fhir.flux_items.get(&name).as_ref().copied()
    }

    pub fn refined_by(self, def_id: LocalDefId) -> QueryResult<&'genv fhir::RefinedBy<'genv>> {
        let refined_by = match &self.expect_item(def_id)?.kind {
            fhir::ItemKind::Enum(enum_def) => enum_def.refined_by,
            fhir::ItemKind::Struct(struct_def) => struct_def.refined_by,
            fhir::ItemKind::TyAlias(ty_alias) => ty_alias.refined_by,
            _ => bug!("expected struct, enum or type alias"),
        };
        Ok(refined_by)
    }

    pub fn spec_funcs(self) -> impl Iterator<Item = &'genv fhir::SpecFunc<'genv>> {
        self.fhir.flux_items.values().filter_map(|item| {
            if let fhir::FluxItem::Func(defn) = item {
                Some(defn)
            } else {
                None
            }
        })
    }

    pub fn spec_func(&self, name: Symbol) -> Option<&'genv fhir::SpecFunc<'genv>> {
        self.fhir.flux_items.get(&name).and_then(|item| {
            if let fhir::FluxItem::Func(defn) = item {
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

    pub fn consts(self) -> impl Iterator<Item = fhir::ConstInfo> + 'genv {
        self.fhir.consts.values().copied()
    }

    pub fn fn_quals_for(self, def_id: LocalDefId) -> QueryResult<&'genv [Ident]> {
        // This is called on adts when checking invariants
        if let Some(fn_sig) = self.node(def_id)?.fn_sig() {
            Ok(fn_sig.qualifiers)
        } else {
            Ok(&[])
        }
    }

    pub fn expect_item(self, def_id: LocalDefId) -> QueryResult<&'genv fhir::Item<'genv>> {
        if let fhir::Node::Item(item) = self.node(def_id)? {
            Ok(item)
        } else {
            bug!("expected item: `{def_id:?}`")
        }
    }

    pub fn node(self, def_id: LocalDefId) -> QueryResult<fhir::Node<'genv>> {
        self.genv.desugar(def_id)
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

impl ErrorEmitter for GlobalEnv<'_, '_> {
    fn emit<'a>(&'a self, err: impl rustc_errors::Diagnostic<'a>) -> rustc_span::ErrorGuaranteed {
        self.sess().emit(err)
    }
}
