use std::collections::{HashMap, hash_map::Entry};

use flux_common::span_bug;
use flux_middle::fhir::Trusted;
use flux_syntax::surface::{self, FnSpec, Item, Span};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    OwnerId,
    def::{DefKind, Res},
    def_id::{CRATE_DEF_ID, LocalDefId},
};
use rustc_middle::ty::{AssocItem, AssocKind, Ty, TyCtxt};
use rustc_span::{Symbol, def_id::DefId};

use crate::collector::{FluxAttrs, SpecCollector, errors, surface::Ident};
type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

#[derive(PartialEq, Eq, Debug, Hash)]
struct ImplKey(Symbol);

impl ImplKey {
    fn new(ty: Ty) -> Self {
        ImplKey(Symbol::intern(&format!("{ty:?}")))
    }
}

type TraitImplKey = (ImplKey, Symbol);

struct DetachedItems {
    items: HashMap<Ident, (surface::Item, Option<DefId>)>,
    inherent_impls: HashMap<Ident, (surface::DetachedInherentImpl, Option<DefId>)>,
    trait_impls: HashMap<TraitImplKey, (surface::DetachedTraitImpl, Option<LocalDefId>, Span)>,
}

impl DetachedItems {
    fn new(detached_specs: surface::DetachedSpecs, collector: &mut SpecCollector) -> Result<Self> {
        let mut items = HashMap::default();
        let mut inherent_impls: HashMap<Ident, (surface::DetachedInherentImpl, Option<DefId>)> =
            HashMap::default();
        let mut trait_impls = HashMap::default();
        for item in detached_specs.items {
            match item.kind {
                surface::ItemKind::InherentImpl(detached_impl) => {
                    if let Some(existing) = inherent_impls.get_mut(&item.ident) {
                        existing.0.extend(detached_impl);
                    } else {
                        inherent_impls.insert(item.ident, (detached_impl, None));
                    }
                }
                surface::ItemKind::TraitImpl(detached_impl) => {
                    let key = (ImplKey(item.ident.name), detached_impl.trait_.name);
                    let span = item.ident.span;
                    if let std::collections::hash_map::Entry::Vacant(e) = trait_impls.entry(key) {
                        e.insert((detached_impl, None, span));
                    } else {
                        return Err(collector.errors.emit(errors::AttrMapErr {
                            span,
                            message: format!("multiple impls for `{}`", item.ident.name),
                        }));
                    }
                }
                _ => {
                    items.insert(item.ident, (item, None));
                }
            }
        }
        Ok(DetachedItems { items, inherent_impls, trait_impls })
    }

    fn resolve(&mut self, collector: &mut SpecCollector, tcx: TyCtxt, scope: LocalDefId) -> Result {
        self.resolve_items(collector, tcx, scope)?;
        self.resolve_inherent_impls(tcx, scope);
        self.resolve_trait_impls(tcx);
        Ok(())
    }

    fn resolve_trait_impls(&mut self, tcx: TyCtxt) {
        for (trait_id, impl_ids) in tcx.all_local_trait_impls(()) {
            if let Some(trait_symbol) = tcx.opt_item_name(*trait_id) {
                for impl_id in impl_ids {
                    if let Some(poly_trait_ref) = tcx.impl_trait_ref(*impl_id) {
                        let impl_key =
                            ImplKey::new(poly_trait_ref.instantiate_identity().self_ty());
                        if let Some(val) = self.trait_impls.get_mut(&(impl_key, trait_symbol)) {
                            val.1 = Some(*impl_id);
                        }
                    }
                }
            }
        }
    }

    fn resolve_inherent_impls(&mut self, tcx: TyCtxt, scope: LocalDefId) {
        for child in tcx.module_children_local(scope) {
            let ident = child.ident;
            if let Res::Def(kind, def_id) = child.res
                && matches!(kind, DefKind::Struct | DefKind::Enum)
                && let Some(val) = self.inherent_impls.get_mut(&ident)
            {
                val.1 = Some(def_id);
            }
        }
    }

    fn expect_kind(
        tcx: TyCtxt,
        collector: &mut SpecCollector,
        def_id: DefId,
        exp_kind: DefKind,
        kind: DefKind,
        span: Span,
    ) -> Result {
        let expected_span = tcx.def_span(def_id);
        let expected = exp_kind.descr(def_id);
        let name = tcx.def_path_str(def_id);
        if kind != exp_kind {
            return Err(collector.errors.emit(errors::UnexpectedSpecification::new(
                name,
                span,
                expected,
                expected_span,
            )));
        }
        Ok(())
    }

    fn resolve_items(
        &mut self,
        collector: &mut SpecCollector,
        tcx: TyCtxt,
        scope: LocalDefId,
    ) -> Result {
        for child in tcx.module_children_local(scope) {
            let ident = child.ident;
            let Res::Def(exp_kind, def_id) = child.res else { continue };
            let Some(val) = self.items.get_mut(&ident) else { continue };
            let span = val.0.ident.span;
            match val.0.kind {
                surface::ItemKind::FnSig(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Fn, span)?
                }
                surface::ItemKind::Mod(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Mod, span)?
                }
                surface::ItemKind::Struct(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Struct, span)?
                }
                surface::ItemKind::Enum(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Enum, span)?
                }
                surface::ItemKind::Trait(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Trait, span)?
                }
                _ => continue,
            }
            if val.1.is_some() {
                span_bug!(val.0.ident.span, "detached item already resolved {val:?}")
            } else {
                val.1 = Some(def_id);
            }
        }
        Ok(())
    }
}

pub(super) struct DetachedSpecsCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
}

impl<'a, 'sess, 'tcx> DetachedSpecsCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(
        inner: &'a mut SpecCollector<'sess, 'tcx>,
        attrs: &mut FluxAttrs,
    ) -> Result {
        if let Some(detached_specs) = attrs.detached_specs() {
            Self { inner }.run(detached_specs, CRATE_DEF_ID)?;
        };
        Ok(())
    }

    fn run(&mut self, detached_specs: surface::DetachedSpecs, parent: LocalDefId) -> Result {
        let mut detached_items = DetachedItems::new(detached_specs, self.inner)?;
        let tcx = self.inner.tcx;

        detached_items.resolve(self.inner, tcx, parent)?;

        for (ident, (item, def_id)) in detached_items.items {
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let owner_id = tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_item(owner_id, item)?;
            }
        }
        for (ident, (inherent_impl, def_id)) in detached_items.inherent_impls {
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let assoc_items = tcx
                    .inherent_impls(def_id)
                    .into_iter()
                    .flat_map(|impl_id| tcx.associated_items(impl_id).in_definition_order());
                self.collect_assoc_methods(inherent_impl.items, assoc_items)?;
            }
        }
        for ((_, _), (trait_impl, impl_id, span)) in detached_items.trait_impls {
            if let Some(impl_id) = impl_id {
                let owner_id = tcx.local_def_id_to_hir_id(impl_id).owner;
                self.collect_trait_impl(owner_id, trait_impl, span)?;
            }
        }
        Ok(())
    }

    #[allow(
        clippy::disallowed_methods,
        reason = "this is pre-extern specs so it's fine: https://flux-rs.zulipchat.com/#narrow/channel/486369-verify-std/topic/detached-specs/near/529548357"
    )]
    fn unwrap_def_id(&mut self, ident: Ident, def_id: Option<DefId>) -> Result<Option<LocalDefId>> {
        let Some(def_id) = def_id else {
            return Err(self
                .inner
                .errors
                .emit(errors::UnresolvedIdentifier { span: ident.span, ident }));
        };
        Ok(def_id.as_local())
    }

    fn err_multiple_specs(&mut self, def_id: DefId, span: Span) -> ErrorGuaranteed {
        let name = self.inner.tcx.def_path_str(def_id);
        self.inner
            .errors
            .emit(errors::MultipleSpecifications { name, span })
    }

    fn collect_trait(
        &mut self,
        ident: Ident,
        owner_id: OwnerId,
        trait_def: surface::DetachedTrait,
    ) -> Result {
        // 1. Collect the associated-refinements
        match self.inner.specs.traits.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(surface::Trait { generics: None, assoc_refinements: trait_def.refts });
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                self.err_multiple_specs(owner_id.to_def_id(), ident.span);
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                existing.assoc_refinements.extend(trait_def.refts);
            }
        }

        // 2. Collect the method specifications
        let tcx = self.inner.tcx;
        let assoc_items = tcx.associated_items(owner_id.def_id).in_definition_order();
        self.collect_assoc_methods(trait_def.items, assoc_items)
    }

    fn collect_trait_impl(
        &mut self,
        owner_id: OwnerId,
        trait_impl: surface::DetachedTraitImpl,
        span: Span,
    ) -> Result {
        // 1. Collect the associated-refinements
        match self.inner.specs.impls.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(surface::Impl { generics: None, assoc_refinements: trait_impl.refts });
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                return Err(self.err_multiple_specs(owner_id.to_def_id(), span));
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                existing.assoc_refinements.extend(trait_impl.refts);
            }
        }

        // 2. Collect the method specifications
        let tcx = self.inner.tcx;
        let assoc_items = tcx.associated_items(owner_id.def_id).in_definition_order();
        self.collect_assoc_methods(trait_impl.items, assoc_items)
    }

    fn collect_enum(
        &mut self,
        ident: Ident,
        owner_id: OwnerId,
        enum_def: surface::EnumDef,
    ) -> Result {
        match self.inner.specs.enums.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(enum_def);
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                return Err(self.err_multiple_specs(owner_id.to_def_id(), ident.span));
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                *existing = enum_def;
            }
        }
        Ok(())
    }

    fn collect_struct(
        &mut self,
        ident: Ident,
        owner_id: OwnerId,
        struct_def: surface::StructDef,
    ) -> Result {
        match self.inner.specs.structs.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(struct_def);
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                return Err(self.err_multiple_specs(owner_id.to_def_id(), ident.span));
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                *existing = struct_def;
            }
        }
        Ok(())
    }

    fn collect_fn_spec(&mut self, owner_id: OwnerId, fn_spec: surface::FnSpec) -> Result {
        match self.inner.specs.fn_sigs.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(fn_spec);
            }
            Entry::Occupied(ref e) if e.get().fn_sig.is_some() => {
                let fn_sig = fn_spec.fn_sig.unwrap();
                return Err(self.err_multiple_specs(owner_id.to_def_id(), fn_sig.span));
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                (*existing).fn_sig = Some(fn_spec.fn_sig.unwrap());
                (*existing).trusted = fn_spec.trusted;
                if fn_spec.trusted {
                    self.inner
                        .specs
                        .trusted
                        .insert(owner_id.def_id, Trusted::Yes);
                }
            }
        }
        Ok(())
    }

    fn collect_assoc_methods(
        &mut self,
        methods: Vec<Item<FnSpec>>,
        assoc_items: impl Iterator<Item = &'tcx AssocItem>,
    ) -> Result {
        let mut table: HashMap<Symbol, (surface::FnSpec, Option<DefId>, Span)> = HashMap::default();
        // 1. make a table of the impl-items
        for item in methods {
            let key = item.ident.name;
            if let Entry::Occupied(_) = table.entry(key) {
                return Err(self.inner.errors.emit(errors::AttrMapErr {
                    span: item.ident.span,
                    message: format!("multiple specs for `{}`", item.ident),
                }));
            } else {
                table.insert(item.ident.name, (item.kind, None, item.ident.span));
            }
        }
        // 2. walk over all the assoc-items to resolve names
        for item in assoc_items {
            if let AssocKind::Fn { name, .. } = item.kind
                && let Some(val) = table.get_mut(&name)
                && val.1.is_none()
            {
                val.1 = Some(item.def_id);
            }
        }
        // 3. Attach the `fn_sig` to the resolved `DefId`
        for (name, (fn_spec, def_id, span)) in table {
            let ident = Ident { name, span };
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_fn_spec(owner_id, fn_spec)?;
            }
        }
        Ok(())
    }

    fn collect_item(&mut self, owner_id: OwnerId, item: surface::Item) -> Result {
        match item.kind {
            surface::ItemKind::FnSig(item) => self.collect_fn_spec(owner_id, item.kind),
            surface::ItemKind::Struct(struct_def) => {
                self.collect_struct(item.ident, owner_id, struct_def)
            }
            surface::ItemKind::Enum(enum_def) => self.collect_enum(item.ident, owner_id, enum_def),
            surface::ItemKind::Mod(detached_specs) => self.run(detached_specs, owner_id.def_id),
            surface::ItemKind::Trait(trait_def) => {
                self.collect_trait(item.ident, owner_id, trait_def)
            }
            _ => {
                span_bug!(item.ident.span, "unexpected detached item!")
            }
        }
    }
}
