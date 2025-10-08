use std::collections::{HashMap, hash_map::Entry};

use flux_common::dbg::{self, SpanTrace};
use flux_syntax::surface::{self, DetachedItem, ExprPath, FnSpec, NodeId};
use itertools::Itertools;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    OwnerId,
    def::{DefKind, Res},
    def_id::LocalDefId,
};
use rustc_middle::ty::{AssocItem, AssocKind, Ty, TyCtxt};
use rustc_span::{Symbol, def_id::DefId};

use crate::collector::{FluxAttrs, SpecCollector, errors};
type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

#[derive(PartialEq, Eq, Debug, Hash, Clone, Copy)]
enum LookupRes {
    DefId(DefId),
    Name(Symbol),
}

impl LookupRes {
    fn from_name<T: std::fmt::Debug>(thing: &T) -> Self {
        let str = format!("{thing:?}");
        LookupRes::Name(Symbol::intern(&str))
    }

    fn new(ty: &Ty) -> Self {
        match ty.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => LookupRes::DefId(adt_def.did()),
            _ => Self::from_name(ty),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Hash)]
struct TraitImplKey {
    trait_: LookupRes,
    self_ty: LookupRes,
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

fn item_def_kind(kind: &surface::DetachedItemKind) -> Vec<DefKind> {
    match kind {
        surface::DetachedItemKind::FnSig(_) => vec![DefKind::Fn],
        surface::DetachedItemKind::Mod(_) => vec![DefKind::Mod],
        surface::DetachedItemKind::Struct(_) => vec![DefKind::Struct],
        surface::DetachedItemKind::Enum(_) => vec![DefKind::Enum],
        surface::DetachedItemKind::InherentImpl(_) | surface::DetachedItemKind::TraitImpl(_) => {
            vec![DefKind::Struct, DefKind::Enum]
        }
        surface::DetachedItemKind::Trait(_) => vec![DefKind::Trait],
    }
}

#[derive(Debug)]
struct ScopeResolver {
    items: HashMap<(Symbol, DefKind), LookupRes>,
}

impl ScopeResolver {
    fn new(tcx: TyCtxt, def_id: LocalDefId, impl_resolver: &TraitImplResolver) -> Self {
        let mut items = HashMap::default();
        for child in tcx.module_children_local(def_id) {
            let ident = child.ident;
            if let Res::Def(exp_kind, def_id) = child.res {
                items.insert((ident.name, exp_kind), LookupRes::DefId(def_id));
            }
        }
        for pty in rustc_hir::PrimTy::ALL {
            let name = pty.name();
            items.insert((name, DefKind::Struct), LookupRes::Name(name)); // HACK: use DefKind::Struct for primitive...
        }
        for trait_impl_key in impl_resolver.items.keys() {
            if let LookupRes::DefId(trait_id) = trait_impl_key.trait_ {
                let name = Symbol::intern(&tcx.def_path_str(trait_id));
                items.insert((name, DefKind::Trait), trait_impl_key.trait_);
            }
        }
        Self { items }
    }

    fn lookup(&self, path: &ExprPath, item_kind: &surface::DetachedItemKind) -> Option<LookupRes> {
        let symbol = path_to_symbol(path);
        for kind in item_def_kind(item_kind) {
            let key = (symbol, kind);
            if let Some(res) = self.items.get(&key) {
                return Some(*res);
            }
        }
        None
    }
}

#[derive(Debug)]
struct TraitImplResolver {
    items: HashMap<TraitImplKey, LocalDefId>,
}

impl TraitImplResolver {
    fn new(tcx: TyCtxt) -> Self {
        let mut items = HashMap::default();
        for (trait_id, impl_ids) in tcx.all_local_trait_impls(()) {
            let trait_ = LookupRes::DefId(*trait_id);
            for impl_id in impl_ids {
                if let Some(poly_trait_ref) = tcx.impl_trait_ref(*impl_id) {
                    let self_ty = poly_trait_ref.instantiate_identity().self_ty();
                    let self_ty = LookupRes::new(&self_ty);
                    let key = TraitImplKey { trait_, self_ty };
                    items.insert(key, *impl_id);
                }
            }
        }
        Self { items }
    }

    fn resolve(&self, trait_: LookupRes, self_ty: LookupRes) -> Option<LocalDefId> {
        let key = TraitImplKey { trait_, self_ty };
        self.items.get(&key).copied()
    }
}

pub(super) struct DetachedSpecsCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
    id_resolver: HashMap<NodeId, LookupRes>,
    impl_resolver: TraitImplResolver,
}

impl<'a, 'sess, 'tcx> DetachedSpecsCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(
        inner: &'a mut SpecCollector<'sess, 'tcx>,
        attrs: &mut FluxAttrs,
        module_id: LocalDefId,
    ) -> Result {
        if let Some(detached_specs) = attrs.detached_specs() {
            let trait_impl_resolver = TraitImplResolver::new(inner.tcx);
            let mut collector =
                Self { inner, id_resolver: HashMap::default(), impl_resolver: trait_impl_resolver };
            collector.run(detached_specs, module_id)?;
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

    fn resolve_path_kind(
        &mut self,
        resolver: &ScopeResolver,
        path: &ExprPath,
        kind: &surface::DetachedItemKind,
    ) -> Result {
        let Some(res) = resolver.lookup(path, kind) else {
            return Err(self
                .inner
                .errors
                .emit(errors::UnresolvedSpecification::new(path, "name")));
        };
        self.id_resolver.insert(path.node_id, res);
        Ok(())
    }

    fn resolve(&mut self, detached_specs: &surface::DetachedSpecs, def_id: LocalDefId) -> Result {
        let resolver = ScopeResolver::new(self.inner.tcx, def_id, &self.impl_resolver);
        for item in &detached_specs.items {
            self.resolve_path_kind(&resolver, &item.path, &item.kind)?;
            if let surface::DetachedItemKind::TraitImpl(trait_impl) = &item.kind {
                let kind = surface::DetachedItemKind::Trait(surface::DetachedTrait::default());
                self.resolve_path_kind(&resolver, &trait_impl.trait_, &kind)?;
            }
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

    fn lookup(&mut self, item: &surface::DetachedItem) -> Result<LocalDefId> {
        let path_def_id = self.id_resolver.get(&item.path.node_id);

        if let surface::DetachedItemKind::TraitImpl(trait_impl) = &item.kind
            && let Some(trait_) = self.id_resolver.get(&trait_impl.trait_.node_id)
            && let Some(self_ty) = path_def_id
            && let Some(impl_id) = self.impl_resolver.resolve(*trait_, *self_ty)
        {
            return Ok(impl_id);
        }
        if let Some(LookupRes::DefId(def_id)) = self.id_resolver.get(&item.path.node_id)
            && let Some(local_def_id) = self.unwrap_def_id(def_id)?
        {
            return Ok(local_def_id);
        }
        Err(self
            .inner
            .errors
            .emit(errors::UnresolvedSpecification::new(&item.path, "item")))
    }

    fn attach(&mut self, item: surface::DetachedItem) -> Result {
        let def_id = self.lookup(&item)?;
        let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
        let span = item.span();
        let dst_span = self.inner.tcx.def_span(def_id);
        dbg::hyperlink!(self.inner.tcx, span, dst_span);
        match item.kind {
            surface::DetachedItemKind::FnSig(fn_spec) => self.collect_fn_spec(owner_id, fn_spec)?,
            surface::DetachedItemKind::Struct(struct_def) => {
                self.collect_struct(owner_id, struct_def)?;
            }
            surface::DetachedItemKind::Enum(enum_def) => self.collect_enum(owner_id, enum_def)?,
            surface::DetachedItemKind::Mod(detached_specs) => {
                self.run(detached_specs, owner_id.def_id)?;
            }
            surface::DetachedItemKind::Trait(trait_def) => {
                self.collect_trait(owner_id, trait_def)?;
            }
            surface::DetachedItemKind::InherentImpl(inherent_impl) => {
                let tcx = self.inner.tcx;
                let assoc_items = tcx
                    .inherent_impls(def_id)
                    .iter()
                    .flat_map(|impl_id| tcx.associated_items(impl_id).in_definition_order());
                self.collect_assoc_methods(inherent_impl.items, assoc_items)?;
            }
            surface::DetachedItemKind::TraitImpl(trait_impl) => {
                self.collect_trait_impl(owner_id, trait_impl)?;
            }
        };
        Ok(())
    }

    fn collect_fn_spec(&mut self, owner_id: OwnerId, fn_spec: surface::FnSpec) -> Result {
        self.inner
            .specs
            .insert_fn_spec(owner_id, fn_spec)
            .map_err(|_| self.inner.err_multiple_specs(owner_id.to_def_id(), None))
    }

    fn collect_struct(&mut self, owner_id: OwnerId, struct_def: surface::StructDef) -> Result {
        self.inner
            .specs
            .insert_struct_def(owner_id, struct_def)
            .map_err(|_| self.inner.err_multiple_specs(owner_id.to_def_id(), None))
    }

    fn collect_enum(&mut self, owner_id: OwnerId, enum_def: surface::EnumDef) -> Result {
        self.inner
            .specs
            .insert_enum_def(owner_id, enum_def)
            .map_err(|_| self.inner.err_multiple_specs(owner_id.to_def_id(), None))
    }

    fn collect_trait(&mut self, owner_id: OwnerId, trait_def: surface::DetachedTrait) -> Result {
        // 1. Collect the associated-refinements
        self.inner
            .specs
            .insert_trait(
                owner_id,
                surface::Trait { generics: None, assoc_refinements: trait_def.refts },
            )
            .map_err(|_| self.inner.err_multiple_specs(owner_id.to_def_id(), None))?;

        // 2. Collect the method specifications
        let tcx = self.inner.tcx;
        let assoc_items = tcx.associated_items(owner_id.def_id).in_definition_order();
        self.collect_assoc_methods(trait_def.items, assoc_items)
    }

    fn collect_trait_impl(
        &mut self,
        owner_id: OwnerId,
        trait_impl: surface::DetachedTraitImpl,
    ) -> Result {
        // 1. Collect the associated-refinements
        self.inner
            .specs
            .insert_impl(
                owner_id,
                surface::Impl { generics: None, assoc_refinements: trait_impl.refts },
            )
            .map_err(|_| self.inner.err_multiple_specs(owner_id.to_def_id(), None))?;

        // 2. Collect the method specifications
        let tcx = self.inner.tcx;
        let assoc_items = tcx.associated_items(owner_id.def_id).in_definition_order();
        self.collect_assoc_methods(trait_impl.items, assoc_items)
    }

    fn collect_assoc_methods(
        &mut self,
        methods: Vec<DetachedItem<FnSpec>>,
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
                dbg::hyperlink!(self.inner.tcx, path.span, self.inner.tcx.def_span(def_id));
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_fn_spec(owner_id, fn_spec)?;
            }
        }
        Ok(())
    }
}
