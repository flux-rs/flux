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
use rustc_middle::ty::{AssocItem, AssocKind, TyCtxt};
use rustc_span::{Symbol, def_id::DefId};

use crate::collector::{FluxAttrs, SpecCollector, errors};
type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

fn path_to_symbol(path: &surface::ExprPath) -> Symbol {
    let path_string = format!(
        "{}",
        path.segments
            .iter()
            .format_with("::", |s, f| f(&s.ident.name))
    );
    Symbol::intern(&path_string)
}

struct ScopeResolver {
    items: HashMap<Symbol, (DefKind, DefId)>,
}

impl ScopeResolver {
    fn new(tcx: TyCtxt, def_id: LocalDefId) -> Self {
        let mut items = HashMap::default();
        for child in tcx.module_children_local(def_id) {
            let ident = child.ident;
            let Res::Def(exp_kind, def_id) = child.res else { continue };
            items.insert(ident.name, (exp_kind, def_id));
        }
        Self { items }
    }

    fn lookup(&self, path: &ExprPath) -> Option<(DefKind, DefId)> {
        let name = path_to_symbol(path);
        self.items.get(&name).cloned()
    }
}

pub(super) struct DetachedSpecsCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
    resolved_ids: HashMap<NodeId, Res>,
}

impl<'a, 'sess, 'tcx> DetachedSpecsCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(
        inner: &'a mut SpecCollector<'sess, 'tcx>,
        attrs: &mut FluxAttrs,
    ) -> Result {
        if let Some(detached_specs) = attrs.detached_specs() {
            let mut collector = Self { inner, resolved_ids: HashMap::default() };
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

    fn expect_kind(&mut self, def_id: DefId, eq: bool, expected: &str, span: Span) -> Result {
        let expected_span = self.inner.tcx.def_span(def_id);
        let name = self.inner.tcx.def_path_str(def_id);
        if !eq {
            return Err(self.inner.errors.emit(errors::UnexpectedSpecification::new(
                name,
                span,
                expected,
                expected_span,
            )));
        }
        Ok(())
    }

    fn resolve(&mut self, detached_specs: &surface::DetachedSpecs, def_id: LocalDefId) -> Result {
        let resolver = ScopeResolver::new(self.inner.tcx, def_id);
        for item in &detached_specs.items {
            let path = &item.path;
            let span = path.span;
            let Some((exp_kind, def_id)) = resolver.lookup(path) else {
                return Err(self
                    .inner
                    .errors
                    .emit(errors::UnresolvedSpecification::new(path, "name")));
            };
            match item.kind {
                surface::ItemKind::FnSig(_) => {
                    self.expect_kind(def_id, exp_kind == DefKind::Fn, "fn", span)?;
                }
                surface::ItemKind::Mod(_) => {
                    self.expect_kind(def_id, exp_kind == DefKind::Mod, "mod", span)?;
                }
                surface::ItemKind::Struct(_) => {
                    self.expect_kind(def_id, exp_kind == DefKind::Struct, "struct", span)?;
                }
                surface::ItemKind::Enum(_) => {
                    self.expect_kind(def_id, exp_kind == DefKind::Enum, "enum", span)?;
                }
                surface::ItemKind::Trait(_) => {
                    self.expect_kind(def_id, exp_kind == DefKind::Trait, "trait", span)?;
                }
                surface::ItemKind::InherentImpl(_) => {
                    let eq = matches!(exp_kind, DefKind::Struct | DefKind::Enum);
                    self.expect_kind(def_id, eq, "struct or enum", span)?;
                }
                surface::ItemKind::TraitImpl(_) => todo!(),
            }
            self.resolved_ids
                .insert(item.path.node_id, Res::Def(exp_kind, def_id));
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

    fn lookup(&mut self, item: &surface::Item) -> Result<(DefKind, LocalDefId)> {
        if let Some(Res::Def(kind, def_id)) = self.resolved_ids.get(&item.path.node_id)
            && let Some(local_def_id) = self.unwrap_def_id(def_id)?
        {
            return Ok((*kind, local_def_id));
        }
        return Err(self
            .inner
            .errors
            .emit(errors::UnresolvedSpecification::new(&item.path, "item")));
    }

    fn attach(&mut self, item: surface::Item) -> Result {
        let (_, def_id) = self.lookup(&item)?;
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
            surface::ItemKind::TraitImpl(_detached_trait_impl) => todo!("attach trait impl"),
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

/*
#[derive(PartialEq, Eq, Debug, Hash)]
struct ImplKey(Symbol);

impl ImplKey {
    fn new(ty: Ty) -> Self {
        ImplKey(Symbol::intern(&format!("{ty:?}")))
    }
}





type TraitImplKey = (ImplKey, Symbol);

#[derive(PartialEq, Eq, Debug, Hash)]
enum IdentRes {
    Unknown,
    DefId(DefId),
    // Prim(Symbol),
}

impl IdentRes {
    fn is_known(&self) -> bool {
        matches!(self, IdentRes::DefId(_))
        // matches!(self, IdentRes::DefId(_) | IdentRes::Prim(_))
    }
}

#[derive(Debug)]
struct ItemInfo {
    item: surface::Item,
    def_id: IdentRes,
}

#[derive(Debug)]
struct InherentImplInfo {
    inherent_impl: surface::DetachedInherentImpl,
    self_ty: IdentRes,
}

#[derive(Debug)]
struct TraitImplInfo {
    trait_impl: surface::DetachedTraitImpl,
    _trait_id: IdentRes,
    _self_ty: IdentRes,
    impl_id: Option<LocalDefId>,
    span: Span,
}

struct DetachedItems {
    /// the `DefId` is that of the item being specified
    items: HashMap<Ident, ItemInfo>,
    /// the `DefId` is that of the type whose inherent impl is being specified
    inherent_impls: HashMap<Ident, InherentImplInfo>,
    /// the `LocalDefId` is that of the trait impl, the `ImplKey` is the type and trait name
    trait_impls: HashMap<TraitImplKey, TraitImplInfo>,
}

impl DetachedItems {
    fn new(detached_specs: surface::DetachedSpecs, collector: &mut SpecCollector) -> Result<Self> {
        let mut items = HashMap::default();
        let mut inherent_impls: HashMap<Ident, InherentImplInfo> = HashMap::default();
        let mut trait_impls = HashMap::default();
        for item in detached_specs.items {
            match item.kind {
                surface::ItemKind::InherentImpl(detached_impl) => {
                    if let Some(existing) = inherent_impls.get_mut(&item.path) {
                        existing.inherent_impl.extend(detached_impl);
                    } else {
                        let info = InherentImplInfo {
                            inherent_impl: detached_impl,
                            self_ty: IdentRes::Unknown,
                        };
                        inherent_impls.insert(item.path, info);
                    }
                }
                surface::ItemKind::TraitImpl(detached_impl) => {
                    let key = (ImplKey(item.path.name), detached_impl.trait_.name);
                    let span = item.path.span;
                    let info = TraitImplInfo {
                        trait_impl: detached_impl,
                        _trait_id: IdentRes::Unknown,
                        _self_ty: IdentRes::Unknown,
                        impl_id: None,
                        span,
                    };
                    if let std::collections::hash_map::Entry::Vacant(e) = trait_impls.entry(key) {
                        e.insert(info);
                    } else {
                        return Err(collector.errors.emit(errors::AttrMapErr {
                            span,
                            message: format!("multiple impls for `{}`", item.path.name),
                        }));
                    }
                }
                _ => {
                    items.insert(item.path, ItemInfo { item, def_id: IdentRes::Unknown });
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
                        let key = (impl_key, trait_symbol);
                        println!("TRACE: resolve_trait_impls: {key:?} => {impl_id:?}");
                        if let Some(val) = self.trait_impls.get_mut(&key) {
                            val.impl_id = Some(*impl_id);
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
                val.self_ty = IdentRes::DefId(def_id);
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
            let span = val.item.path.span;
            match val.item.kind {
                surface::ItemKind::FnSig(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Fn, span)?;
                }
                surface::ItemKind::Mod(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Mod, span)?;
                }
                surface::ItemKind::Struct(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Struct, span)?;
                }
                surface::ItemKind::Enum(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Enum, span)?;
                }
                surface::ItemKind::Trait(_) => {
                    Self::expect_kind(tcx, collector, def_id, exp_kind, DefKind::Trait, span)?;
                }
                _ => continue,
            }
            if val.def_id.is_known() {
                span_bug!(span, "detached item already resolved {val:?}");
            } else {
                val.def_id = IdentRes::DefId(def_id);
            }
        }
        Ok(())
    }
}



impl<'a, 'sess, 'tcx> DetachedSpecsCollector<'a, 'sess, 'tcx> {
    fn new(inner: &'a mut SpecCollector<'sess, 'tcx>) -> Self {
        Self { inner, resolved_ids: HashMap::default() }
    }

    pub(super) fn collect(
        inner: &'a mut SpecCollector<'sess, 'tcx>,
        attrs: &mut FluxAttrs,
    ) -> Result {
        if let Some(detached_specs) = attrs.detached_specs() {
            let mut collector = Self::new(inner);
            collector.resolve(&detached_specs, CRATE_DEF_ID)?;
            collector.attach_detached_specs(&detached_specs)?;
            // Self { inner }.run(detached_specs, CRATE_DEF_ID)?;
        };
        Ok(())
    }

    fn resolve(&mut self, detached_specs: &surface::DetachedSpecs, scope: LocalDefId) -> Result {
        for item in detached_specs.items {
            match item.kind {
                surface::ItemKind::FnSig(fn_spec) => todo!(),
                surface::ItemKind::Mod(detached_specs) => todo!(),
                surface::ItemKind::Struct(struct_def) => todo!(),
                surface::ItemKind::Enum(enum_def) => todo!(),
                surface::ItemKind::InherentImpl(detached_inherent_impl) => todo!(),
                surface::ItemKind::TraitImpl(detached_trait_impl) => todo!(),
                surface::ItemKind::Trait(detached_trait) => todo!(),
            }
        }
        Ok(())
    }

    fn run(&mut self, detached_specs: surface::DetachedSpecs, parent: LocalDefId) -> Result {
        let mut detached_items = DetachedItems::new(detached_specs, self.inner)?;
        let tcx = self.inner.tcx;

        detached_items.resolve(self.inner, tcx, parent)?;

        for (ident, ItemInfo { item, def_id }) in detached_items.items {
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let owner_id = tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_item(owner_id, item)?;
            }
        }
        for (ident, InherentImplInfo { inherent_impl, self_ty }) in detached_items.inherent_impls {
            if let Some(def_id) = self.unwrap_def_id(ident, self_ty)? {
                let assoc_items = tcx
                    .inherent_impls(def_id)
                    .iter()
                    .flat_map(|impl_id| tcx.associated_items(impl_id).in_definition_order());
                self.collect_assoc_methods(inherent_impl.items, assoc_items)?;
            }
        }
        for ((_, _), info) in detached_items.trait_impls {
            if let Some(impl_id) = info.impl_id {
                let owner_id = tcx.local_def_id_to_hir_id(impl_id).owner;
                self.collect_trait_impl(owner_id, info.trait_impl, info.span)?;
            } else {
                let ident = info.trait_impl.trait_;
                return Err(self
                    .inner
                    .errors
                    .emit(errors::UnresolvedSpecification::new(ident, "trait implementation")));
            }
        }
        Ok(())
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


    fn collect_item(&mut self, owner_id: OwnerId, item: surface::Item) -> Result {
        match item.kind {
            surface::ItemKind::FnSig(item) => self.collect_fn_spec(owner_id, item.kind),
            surface::ItemKind::Struct(struct_def) => {
                self.collect_struct(item.path, owner_id, struct_def)
            }
            surface::ItemKind::Enum(enum_def) => self.collect_enum(item.path, owner_id, enum_def),
            surface::ItemKind::Mod(detached_specs) => self.run(detached_specs, owner_id.def_id),
            surface::ItemKind::Trait(trait_def) => {
                self.collect_trait(item.path, owner_id, trait_def)
            }
            _ => {
                span_bug!(item.path.span, "unexpected detached item!")
            }
        }
    }
}

*/
