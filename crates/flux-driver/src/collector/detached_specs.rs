use std::collections::{HashMap, hash_map::Entry};

use flux_middle::fhir::Trusted;
use flux_syntax::surface::{self, ExprPath, FnSpec, Item, NodeId, Span};
use itertools::Itertools;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    OwnerId,
    def::{DefKind, Res},
    def_id::{CRATE_DEF_ID, LocalDefId},
};
use rustc_middle::ty::{AssocItem, AssocKind, Ty, TyCtxt};
use rustc_span::{Symbol, def_id::DefId};

use crate::collector::{FluxAttrs, SpecCollector, errors};
type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

#[derive(PartialEq, Eq, Debug, Hash)]
struct ImplKey(Symbol);

impl ImplKey {
    fn new(ty: &Ty) -> Self {
        ImplKey(Symbol::intern(&format!("{ty:?}")))
    }
}

#[derive(PartialEq, Eq, Debug, Hash)]
struct TraitImplKey {
    trait_: Symbol,
    self_ty: ImplKey,
}

fn path_to_symbol(path: &surface::ExprPath) -> Symbol {
    let path_string = format!(
        "{}",
        path.segments
            .iter()
            .format_with("::", |s, f| f(&s.ident.name))
    );
    Symbol::intern(&path_string)
}
fn item_def_kind(kind: &surface::ItemKind) -> Vec<DefKind> {
    match kind {
        surface::ItemKind::FnSig(_) => vec![DefKind::Fn],
        surface::ItemKind::Mod(_) => vec![DefKind::Mod],
        surface::ItemKind::Struct(_) => vec![DefKind::Struct],
        surface::ItemKind::Enum(_) => vec![DefKind::Enum],
        surface::ItemKind::InherentImpl(_) | surface::ItemKind::TraitImpl(_) => {
            vec![DefKind::Struct, DefKind::Enum]
        }
        surface::ItemKind::Trait(_) => vec![DefKind::Trait],
    }
}

struct ScopeResolver {
    items: HashMap<(Symbol, DefKind), DefId>,
}

impl ScopeResolver {
    fn new(tcx: TyCtxt, def_id: LocalDefId) -> Self {
        let mut items = HashMap::default();
        for child in tcx.module_children_local(def_id) {
            let ident = child.ident;
            if let Res::Def(exp_kind, def_id) = child.res {
                items.insert((ident.name, exp_kind), def_id);
            }
        }
        Self { items }
    }

    fn lookup(&self, path: &ExprPath, item_kind: &surface::ItemKind) -> Option<DefId> {
        let symbol = path_to_symbol(path);
        for kind in item_def_kind(item_kind) {
            let key = (symbol, kind);
            if let Some(def_id) = self.items.get(&key) {
                return Some(*def_id);
            }
        }
        None
    }
}

struct TraitImplResolver {
    items: HashMap<TraitImplKey, LocalDefId>,
}

impl TraitImplResolver {
    fn new(tcx: TyCtxt) -> Self {
        let mut items = HashMap::default();
        for (trait_id, impl_ids) in tcx.all_local_trait_impls(()) {
            if let Some(trait_) = tcx.opt_item_name(*trait_id) {
                for impl_id in impl_ids {
                    if let Some(poly_trait_ref) = tcx.impl_trait_ref(*impl_id) {
                        let self_ty = poly_trait_ref.instantiate_identity().self_ty();
                        let self_ty = ImplKey::new(&self_ty);
                        let key = TraitImplKey { trait_, self_ty };
                        // println!("TRACE: resolve_trait_impls: {key:?} => {impl_id:?}");
                        items.insert(key, *impl_id);
                    }
                }
            }
        }
        Self { items }
    }

    fn resolve(&self, trait_: &ExprPath, self_ty: &ExprPath) -> Option<LocalDefId> {
        let trait_ = path_to_symbol(trait_);
        let self_ty = ImplKey(path_to_symbol(self_ty));
        let key = TraitImplKey { trait_, self_ty };
        self.items.get(&key).copied()
    }
}

pub(super) struct DetachedSpecsCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
    id_resolver: HashMap<NodeId, DefId>,
    impl_resolver: TraitImplResolver,
}

impl<'a, 'sess, 'tcx> DetachedSpecsCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(
        inner: &'a mut SpecCollector<'sess, 'tcx>,
        attrs: &mut FluxAttrs,
    ) -> Result {
        if let Some(detached_specs) = attrs.detached_specs() {
            let trait_impl_resolver = TraitImplResolver::new(inner.tcx);
            let mut collector =
                Self { inner, id_resolver: HashMap::default(), impl_resolver: trait_impl_resolver };
            collector.run(detached_specs, CRATE_DEF_ID)?;
        };
        Ok(())
    }

    fn run(&mut self, detached_specs: surface::DetachedSpecs, def_id: LocalDefId) -> Result {
        self.resolve(&detached_specs, def_id)?;
        for item in detached_specs.items {
            self.attach(item)?;
        }
        Ok(())
    }

    fn resolve(&mut self, detached_specs: &surface::DetachedSpecs, def_id: LocalDefId) -> Result {
        let resolver = ScopeResolver::new(self.inner.tcx, def_id);
        for item in &detached_specs.items {
            if matches!(item.kind, surface::ItemKind::TraitImpl(_)) {
                continue;
            }
            let path = &item.path;
            let Some(def_id) = resolver.lookup(path, &item.kind) else {
                return Err(self
                    .inner
                    .errors
                    .emit(errors::UnresolvedSpecification::new(path, "name")));
            };
            self.id_resolver.insert(item.path.node_id, def_id);
        }
        Ok(())
    }

    #[allow(
        clippy::disallowed_methods,
        reason = "this is pre-extern specs so it's fine: https://flux-rs.zulipchat.com/#narrow/channel/486369-verify-std/topic/detached-specs/near/529548357"
    )]
    fn unwrap_def_id(&self, def_id: &DefId) -> Result<Option<LocalDefId>> {
        Ok(def_id.as_local())
    }

    fn lookup(&mut self, item: &surface::Item) -> Result<LocalDefId> {
        if let Some(def_id) = self.id_resolver.get(&item.path.node_id)
            && let Some(local_def_id) = self.unwrap_def_id(def_id)?
        {
            return Ok(local_def_id);
        }
        if let surface::ItemKind::TraitImpl(trait_impl) = &item.kind
            && let Some(impl_id) = self.impl_resolver.resolve(&trait_impl.trait_, &item.path)
        {
            return Ok(impl_id);
        }
        return Err(self
            .inner
            .errors
            .emit(errors::UnresolvedSpecification::new(&item.path, "item")));
    }

    fn attach(&mut self, item: surface::Item) -> Result {
        let def_id = self.lookup(&item)?;
        let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
        let span = item.path.span;
        match item.kind {
            surface::ItemKind::FnSig(fn_spec) => self.collect_fn_spec(owner_id, fn_spec)?,
            surface::ItemKind::Struct(struct_def) => {
                self.collect_struct(span, owner_id, struct_def)?
            }
            surface::ItemKind::Enum(enum_def) => self.collect_enum(span, owner_id, enum_def)?,
            surface::ItemKind::Mod(detached_specs) => self.run(detached_specs, owner_id.def_id)?,
            surface::ItemKind::Trait(trait_def) => self.collect_trait(span, owner_id, trait_def)?,
            surface::ItemKind::InherentImpl(inherent_impl) => {
                let tcx = self.inner.tcx;
                let assoc_items = tcx
                    .inherent_impls(def_id)
                    .iter()
                    .flat_map(|impl_id| tcx.associated_items(impl_id).in_definition_order());
                self.collect_assoc_methods(inherent_impl.items, assoc_items)?;
            }
            surface::ItemKind::TraitImpl(trait_impl) => {
                self.collect_trait_impl(owner_id, trait_impl, span)?;
            }
        };
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
                existing.fn_sig = Some(fn_spec.fn_sig.unwrap());
                existing.trusted = fn_spec.trusted;
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

    fn collect_struct(
        &mut self,
        span: Span,
        owner_id: OwnerId,
        struct_def: surface::StructDef,
    ) -> Result {
        match self.inner.specs.structs.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(struct_def);
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                return Err(self.err_multiple_specs(owner_id.to_def_id(), span));
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                *existing = struct_def;
            }
        }
        Ok(())
    }

    fn collect_enum(
        &mut self,
        span: Span,
        owner_id: OwnerId,
        enum_def: surface::EnumDef,
    ) -> Result {
        match self.inner.specs.enums.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(enum_def);
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                return Err(self.err_multiple_specs(owner_id.to_def_id(), span));
            }
            Entry::Occupied(ref mut e) => {
                let existing = e.get_mut();
                *existing = enum_def;
            }
        }
        Ok(())
    }

    fn collect_trait(
        &mut self,
        span: Span,
        owner_id: OwnerId,
        trait_def: surface::DetachedTrait,
    ) -> Result {
        // 1. Collect the associated-refinements
        match self.inner.specs.traits.entry(owner_id) {
            Entry::Vacant(v) => {
                v.insert(surface::Trait { generics: None, assoc_refinements: trait_def.refts });
            }
            Entry::Occupied(ref e) if e.get().is_nontrivial() => {
                self.err_multiple_specs(owner_id.to_def_id(), span);
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

    fn collect_assoc_methods(
        &mut self,
        methods: Vec<Item<FnSpec>>,
        assoc_items: impl Iterator<Item = &'tcx AssocItem>,
    ) -> Result {
        let mut table: HashMap<Symbol, (surface::FnSpec, Option<DefId>, ExprPath)> =
            HashMap::default();
        // 1. make a table of the impl-items
        for item in methods {
            let name = path_to_symbol(&item.path);
            let span = item.path.span;
            if let Entry::Occupied(_) = table.entry(name) {
                return Err(self
                    .inner
                    .errors
                    .emit(errors::MultipleSpecifications { name, span }));
            } else {
                table.insert(name, (item.kind, None, item.path));
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
        for (_name, (fn_spec, def_id, path)) in table {
            let Some(def_id) = def_id else {
                return Err(self
                    .inner
                    .errors
                    .emit(errors::UnresolvedSpecification::new(&path, "identifier")));
            };
            if let Some(def_id) = self.unwrap_def_id(&def_id)? {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_fn_spec(owner_id, fn_spec)?;
            }
        }
        Ok(())
    }

    fn err_multiple_specs(&mut self, def_id: DefId, span: Span) -> ErrorGuaranteed {
        let name = self.inner.tcx.def_path_str(def_id);
        let name = Symbol::intern(&name);
        self.inner
            .errors
            .emit(errors::MultipleSpecifications { name, span })
    }
}
