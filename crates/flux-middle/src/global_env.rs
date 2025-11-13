use std::{alloc, ptr, rc::Rc, slice};

use flux_arc_interner::List;
use flux_common::{bug, result::ErrorEmitter};
use flux_config as config;
use flux_errors::FluxSession;
use flux_rustc_bridge::{self, lowering::Lower, mir, ty};
use rustc_data_structures::unord::UnordSet;
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LocalDefId},
};
use rustc_middle::{
    query::IntoQueryParam,
    ty::{TyCtxt, Variance},
};
use rustc_span::Span;
pub use rustc_span::{Symbol, symbol::Ident};

use crate::{
    cstore::CrateStoreDyn,
    def_id::{FluxDefId, FluxLocalDefId, MaybeExternId, ResolvedDefId},
    fhir::{self, VariantIdx},
    queries::{Providers, Queries, QueryErr, QueryResult},
    query_bug,
    rty::{
        self,
        refining::{Refine as _, Refiner},
    },
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

    pub fn fhir_attr_map(self, def_id: LocalDefId) -> fhir::AttrMap<'genv> {
        self.inner.queries.fhir_attr_map(self, def_id)
    }

    pub fn fhir_crate(self) -> &'genv fhir::FluxItems<'genv> {
        self.inner.queries.fhir_crate(self)
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

    pub fn def_kind(&self, def_id: impl IntoQueryParam<DefId>) -> DefKind {
        self.tcx().def_kind(def_id.into_query_param())
    }

    /// Allocates space to store `cap` elements of type `T`.
    ///
    /// The elements are initialized using the supplied iterator. At most `cap` elements will be
    /// retrieved from the iterator. If the iterator yields fewer than `cap` elements, the returned
    /// slice will be of length less than the allocated capacity.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice fails.
    pub fn alloc_slice_with_capacity<T, I>(self, cap: usize, it: I) -> &'genv [T]
    where
        I: IntoIterator<Item = T>,
    {
        let layout = alloc::Layout::array::<T>(cap).unwrap_or_else(|_| bug!("out of memory"));
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

    pub fn normalized_info(self, did: FluxDefId) -> rty::NormalizeInfo {
        self.normalized_defns(did.krate()).func_info(did).clone()
    }

    pub fn normalized_defns(self, krate: CrateNum) -> Rc<rty::NormalizedDefns> {
        self.inner.queries.normalized_defns(self, krate)
    }

    pub fn prim_rel_for(self, op: &rty::BinOp) -> QueryResult<Option<&'genv rty::PrimRel>> {
        Ok(self.inner.queries.prim_rel(self)?.get(op))
    }

    pub fn qualifiers(self) -> QueryResult<&'genv [rty::Qualifier]> {
        self.inner.queries.qualifiers(self)
    }

    /// Return all the qualifiers that apply to an item, including both global and local qualifiers.
    pub fn qualifiers_for(
        self,
        did: LocalDefId,
    ) -> QueryResult<impl Iterator<Item = &'genv rty::Qualifier>> {
        let quals = self.fhir_attr_map(did).qualifiers;
        let names: UnordSet<_> = quals.iter().copied().collect();
        Ok(self
            .qualifiers()?
            .iter()
            .filter(move |qual| qual.global || names.contains(&qual.def_id)))
    }

    /// Return the list of flux function definitions that should be revelaed for item
    pub fn reveals_for(self, did: LocalDefId) -> &'genv [FluxDefId] {
        self.fhir_attr_map(did).reveals
    }

    pub fn func_sort(self, def_id: impl IntoQueryParam<FluxDefId>) -> rty::PolyFuncSort {
        self.inner
            .queries
            .func_sort(self, def_id.into_query_param())
    }

    pub fn func_span(self, def_id: impl IntoQueryParam<FluxDefId>) -> Span {
        self.inner
            .queries
            .func_span(self, def_id.into_query_param())
    }

    pub fn should_inline_fun(self, def_id: FluxDefId) -> bool {
        let is_poly = self.func_sort(def_id).params().len() > 0;
        is_poly || !flux_config::smt_define_fun()
    }

    pub fn variances_of(self, did: DefId) -> &'tcx [Variance] {
        self.tcx().variances_of(did)
    }

    pub fn mir(self, def_id: LocalDefId) -> QueryResult<Rc<mir::BodyRoot<'tcx>>> {
        self.inner.queries.mir(self, def_id)
    }

    pub fn lower_generics_of(self, def_id: impl IntoQueryParam<DefId>) -> ty::Generics<'tcx> {
        self.inner
            .queries
            .lower_generics_of(self, def_id.into_query_param())
    }

    pub fn lower_predicates_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<ty::GenericPredicates> {
        self.inner
            .queries
            .lower_predicates_of(self, def_id.into_query_param())
    }

    pub fn lower_type_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<ty::EarlyBinder<ty::Ty>> {
        self.inner
            .queries
            .lower_type_of(self, def_id.into_query_param())
    }

    pub fn lower_fn_sig(
        self,
        def_id: impl Into<DefId>,
    ) -> QueryResult<ty::EarlyBinder<ty::PolyFnSig>> {
        self.inner.queries.lower_fn_sig(self, def_id.into())
    }

    pub fn adt_def(self, def_id: impl IntoQueryParam<DefId>) -> QueryResult<rty::AdtDef> {
        self.inner.queries.adt_def(self, def_id.into_query_param())
    }

    pub fn constant_info(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::ConstantInfo> {
        self.inner
            .queries
            .constant_info(self, def_id.into_query_param())
    }

    pub fn adt_sort_def_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::AdtSortDef> {
        self.inner
            .queries
            .adt_sort_def_of(self, def_id.into_query_param())
    }

    pub fn sort_decl_param_count(self, def_id: impl IntoQueryParam<FluxDefId>) -> usize {
        self.inner
            .queries
            .sort_decl_param_count(self, def_id.into_query_param())
    }

    pub fn check_wf(self, def_id: LocalDefId) -> QueryResult<Rc<rty::WfckResults>> {
        self.inner.queries.check_wf(self, def_id)
    }

    pub fn impl_trait_ref(
        self,
        impl_id: DefId,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::TraitRef>>> {
        let Some(trait_ref) = self.tcx().impl_trait_ref(impl_id) else { return Ok(None) };
        let trait_ref = trait_ref.skip_binder();
        let trait_ref = trait_ref
            .lower(self.tcx())
            .map_err(|err| QueryErr::unsupported(trait_ref.def_id, err.into_err()))?
            .refine(&Refiner::default_for_item(self, impl_id)?)?;
        Ok(Some(rty::EarlyBinder(trait_ref)))
    }

    pub fn generics_of(self, def_id: impl IntoQueryParam<DefId>) -> QueryResult<rty::Generics> {
        self.inner
            .queries
            .generics_of(self, def_id.into_query_param())
    }

    pub fn refinement_generics_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::RefinementGenerics>> {
        self.inner
            .queries
            .refinement_generics_of(self, def_id.into_query_param())
    }

    pub fn predicates_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        self.inner
            .queries
            .predicates_of(self, def_id.into_query_param())
    }

    pub fn assoc_refinements_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::AssocRefinements> {
        self.inner
            .queries
            .assoc_refinements_of(self, def_id.into_query_param())
    }

    pub fn assoc_refinement(self, assoc_id: FluxDefId) -> QueryResult<rty::AssocReft> {
        Ok(self.assoc_refinements_of(assoc_id.parent())?.get(assoc_id))
    }

    /// Given the id of an associated refinement in a trait definition returns the body for the
    /// corresponding associated refinement in the implementation with id `impl_id`.
    ///
    /// This function returns [`QueryErr::MissingAssocReft`] if the associated refinement is not
    /// found in the implementation and there's no default body in the trait. This can happen if an
    /// extern spec adds an associated refinement without a default body because we are currently
    /// not checking `compare_impl_item` for those definitions.
    pub fn assoc_refinement_body_for_impl(
        self,
        trait_assoc_id: FluxDefId,
        impl_id: DefId,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        // Check if the implementation has the associated refinement
        let impl_assoc_refts = self.assoc_refinements_of(impl_id)?;
        if let Some(impl_assoc_reft) = impl_assoc_refts.find(trait_assoc_id.name()) {
            return self.assoc_refinement_body(impl_assoc_reft.def_id());
        }

        // Otherwise, check if the trait has a default body
        if let Some(body) = self.default_assoc_refinement_body(trait_assoc_id)? {
            let impl_trait_ref = self
                .impl_trait_ref(impl_id)?
                .unwrap()
                .instantiate_identity();
            return Ok(rty::EarlyBinder(body.instantiate(self.tcx(), &impl_trait_ref.args, &[])));
        }

        Err(QueryErr::MissingAssocReft {
            impl_id,
            trait_id: trait_assoc_id.parent(),
            name: trait_assoc_id.name(),
        })
    }

    pub fn default_assoc_refinement_body(
        self,
        trait_assoc_id: FluxDefId,
    ) -> QueryResult<Option<rty::EarlyBinder<rty::Lambda>>> {
        self.inner
            .queries
            .default_assoc_refinement_body(self, trait_assoc_id)
    }

    pub fn assoc_refinement_body(
        self,
        impl_assoc_id: FluxDefId,
    ) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
        self.inner
            .queries
            .assoc_refinement_body(self, impl_assoc_id)
    }

    pub fn sort_of_assoc_reft(
        self,
        assoc_id: FluxDefId,
    ) -> QueryResult<rty::EarlyBinder<rty::FuncSort>> {
        self.inner.queries.sort_of_assoc_reft(self, assoc_id)
    }

    pub fn item_bounds(self, def_id: DefId) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
        self.inner.queries.item_bounds(self, def_id)
    }

    pub fn type_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::TyOrCtor>> {
        self.inner.queries.type_of(self, def_id.into_query_param())
    }

    pub fn fn_sig(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
        self.inner.queries.fn_sig(self, def_id.into_query_param())
    }

    pub fn variants_of(
        self,
        def_id: impl IntoQueryParam<DefId>,
    ) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        self.inner
            .queries
            .variants_of(self, def_id.into_query_param())
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
    ) -> QueryResult<List<ty::BoundVariableKind>> {
        self.inner.queries.lower_late_bound_vars(self, def_id)
    }

    /// Whether the function is marked with `#[flux::no_panic]`
    pub fn no_panic(self, def_id: impl IntoQueryParam<DefId>) -> bool {
        self.inner.queries.no_panic(self, def_id.into_query_param())
    }

    pub fn is_box(&self, res: fhir::Res) -> bool {
        res.is_box(self.tcx())
    }

    pub fn def_id_to_param_index(&self, def_id: DefId) -> u32 {
        let parent = self.tcx().parent(def_id);
        let generics = self.tcx().generics_of(parent);
        generics.param_def_id_to_index(self.tcx(), def_id).unwrap()
    }

    pub(crate) fn cstore(self) -> &'genv CrateStoreDyn {
        &*self.inner.cstore
    }

    pub fn has_trusted_impl(&self, def_id: DefId) -> bool {
        if let Some(did) = self
            .resolve_id(def_id)
            .as_maybe_extern()
            .map(|id| id.local_id())
        {
            self.trusted_impl(did)
        } else {
            false
        }
    }

    /// The `Output` associated type is defined in `FnOnce`, and `Fn`/`FnMut`
    /// inherit it, so this should suffice to check if the `def_id`
    /// corresponds to `LangItem::FnOnceOutput`.
    pub fn is_fn_output(&self, def_id: DefId) -> bool {
        let def_span = self.tcx().def_span(def_id);
        self.tcx()
            .require_lang_item(rustc_hir::LangItem::FnOnceOutput, def_span)
            == def_id
    }

    /// Iterator over all local def ids that are not a extern spec
    pub fn iter_local_def_id(self) -> impl Iterator<Item = LocalDefId> + use<'tcx, 'genv> {
        self.tcx().iter_local_def_id().filter(move |&local_def_id| {
            self.maybe_extern_id(local_def_id).is_local() && !self.is_dummy(local_def_id)
        })
    }

    pub fn iter_extern_def_id(self) -> impl Iterator<Item = DefId> + use<'tcx, 'genv> {
        self.tcx()
            .iter_local_def_id()
            .filter_map(move |local_def_id| self.maybe_extern_id(local_def_id).as_extern())
    }

    pub fn maybe_extern_id(self, local_id: LocalDefId) -> MaybeExternId {
        self.collect_specs()
            .local_id_to_extern_id
            .get(&local_id)
            .map_or_else(
                || MaybeExternId::Local(local_id),
                |def_id| MaybeExternId::Extern(local_id, *def_id),
            )
    }

    #[expect(clippy::disallowed_methods)]
    pub fn resolve_id(self, def_id: DefId) -> ResolvedDefId {
        let maybe_extern_spec = self
            .collect_specs()
            .extern_id_to_local_id
            .get(&def_id)
            .copied();
        if let Some(local_id) = maybe_extern_spec {
            ResolvedDefId::ExternSpec(local_id, def_id)
        } else if let Some(local_id) = def_id.as_local() {
            debug_assert!(
                self.maybe_extern_id(local_id).is_local(),
                "def id points to dummy local item `{def_id:?}`"
            );
            ResolvedDefId::Local(local_id)
        } else {
            ResolvedDefId::Extern(def_id)
        }
    }

    pub fn infer_opts(self, def_id: LocalDefId) -> config::InferOpts {
        let mut opts = config::PartialInferOpts::default();
        self.traverse_parents(def_id, |did| {
            if let Some(o) = self.fhir_attr_map(did).infer_opts() {
                opts.merge(&o);
            }
            None::<!>
        });
        opts.into()
    }

    /// Transitively follow the parent-chain of `def_id` to find the first containing item with an
    /// explicit `#[flux::trusted(..)]` annotation and return whether that item is trusted or not.
    /// If no explicit annotation is found, return `false`.
    pub fn trusted(self, def_id: LocalDefId) -> bool {
        self.traverse_parents(def_id, |did| self.fhir_attr_map(did).trusted())
            .map(|trusted| trusted.to_bool())
            .unwrap_or_else(config::trusted_default)
    }

    pub fn trusted_impl(self, def_id: LocalDefId) -> bool {
        self.traverse_parents(def_id, |did| self.fhir_attr_map(did).trusted_impl())
            .map(|trusted| trusted.to_bool())
            .unwrap_or(false)
    }

    /// Whether the item is a dummy item created by the extern spec macro.
    ///
    /// See [`crate::Specs::dummy_extern`]
    pub fn is_dummy(self, def_id: LocalDefId) -> bool {
        self.traverse_parents(def_id, |did| {
            self.collect_specs()
                .dummy_extern
                .contains(&did)
                .then_some(())
        })
        .is_some()
    }

    /// Transitively follow the parent-chain of `def_id` to find the first containing item with an
    /// explicit `#[flux::ignore(..)]` annotation and return whether that item is ignored or not.
    /// If no explicit annotation is found, return `false`.
    pub fn ignored(self, def_id: LocalDefId) -> bool {
        self.traverse_parents(def_id, |did| self.fhir_attr_map(did).ignored())
            .map(|ignored| ignored.to_bool())
            .unwrap_or_else(config::ignore_default)
    }

    /// Whether the function is marked with `#[flux::should_fail]`
    pub fn should_fail(self, def_id: LocalDefId) -> bool {
        self.fhir_attr_map(def_id).should_fail()
    }

    /// Whether the function is marked with `#[proven_externally]`
    pub fn proven_externally(self, def_id: LocalDefId) -> bool {
        self.fhir_attr_map(def_id).proven_externally()
    }

    /// Traverse the parent chain of `def_id` until the first node for which `f` returns [`Some`].
    fn traverse_parents<T>(
        self,
        mut def_id: LocalDefId,
        mut f: impl FnMut(LocalDefId) -> Option<T>,
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
}

impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    pub fn fhir_iter_flux_items(
        self,
    ) -> impl Iterator<Item = (FluxLocalDefId, fhir::FluxItem<'genv>)> {
        self.fhir_crate()
            .items
            .iter()
            .map(|(id, item)| (*id, *item))
    }

    pub fn fhir_sort_decl(&self, def_id: FluxLocalDefId) -> Option<&fhir::SortDecl> {
        self.fhir_crate().items.get(&def_id).and_then(|item| {
            if let fhir::FluxItem::SortDecl(sort_decl) = item { Some(*sort_decl) } else { None }
        })
    }

    pub fn fhir_spec_func_body(
        &self,
        def_id: FluxLocalDefId,
    ) -> Option<&'genv fhir::SpecFunc<'genv>> {
        self.fhir_crate()
            .items
            .get(&def_id)
            .and_then(|item| if let fhir::FluxItem::Func(defn) = item { Some(*defn) } else { None })
    }

    pub fn fhir_qualifiers(self) -> impl Iterator<Item = &'genv fhir::Qualifier<'genv>> {
        self.fhir_crate().items.values().filter_map(|item| {
            if let fhir::FluxItem::Qualifier(qual) = item { Some(*qual) } else { None }
        })
    }

    pub fn fhir_primop_props(self) -> impl Iterator<Item = &'genv fhir::PrimOpProp<'genv>> {
        self.fhir_crate().items.values().filter_map(|item| {
            if let fhir::FluxItem::PrimOpProp(prop) = item { Some(*prop) } else { None }
        })
    }

    pub fn fhir_get_generics(
        self,
        def_id: LocalDefId,
    ) -> QueryResult<Option<&'genv fhir::Generics<'genv>>> {
        // We don't have nodes for closures and coroutines
        if matches!(self.def_kind(def_id), DefKind::Closure) {
            Ok(None)
        } else {
            Ok(Some(self.fhir_expect_owner_node(def_id)?.generics()))
        }
    }

    pub fn fhir_expect_refinement_kind(
        self,
        def_id: LocalDefId,
    ) -> QueryResult<&'genv fhir::RefinementKind<'genv>> {
        let kind = match &self.fhir_expect_item(def_id)?.kind {
            fhir::ItemKind::Enum(enum_def) => &enum_def.refinement,
            fhir::ItemKind::Struct(struct_def) => &struct_def.refinement,
            _ => bug!("expected struct, enum or type alias"),
        };
        Ok(kind)
    }

    pub fn fhir_expect_item(self, def_id: LocalDefId) -> QueryResult<&'genv fhir::Item<'genv>> {
        if let fhir::Node::Item(item) = self.fhir_node(def_id)? {
            Ok(item)
        } else {
            Err(query_bug!(def_id, "expected item: `{def_id:?}`"))
        }
    }

    pub fn fhir_expect_owner_node(self, def_id: LocalDefId) -> QueryResult<fhir::OwnerNode<'genv>> {
        let Some(owner) = self.fhir_node(def_id)?.as_owner() else {
            return Err(query_bug!(def_id, "cannot find owner node"));
        };
        Ok(owner)
    }

    pub fn fhir_node(self, def_id: LocalDefId) -> QueryResult<fhir::Node<'genv>> {
        self.desugar(def_id)
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
