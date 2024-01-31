mod refinement_resolver;

use std::collections::hash_map;

use flux_common::bug;
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, Res},
    global_env::GlobalEnv,
    ResolverOutput, Specs,
};
use flux_syntax::surface::{self, visit::Visitor as _, BaseTyKind, Ident};
use hir::{
    def::{DefKind, Namespace::TypeNS},
    intravisit::Visitor as _,
    ItemId, ItemKind, OwnerId,
};
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::FxHashMap;
use rustc_hir as hir;
use rustc_middle::{metadata::ModChild, ty::TyCtxt};
use rustc_span::{
    def_id::{CrateNum, DefId},
    Span, Symbol,
};

use self::refinement_resolver::{RefinementResolver, ScopedVisitor as _};
use crate::sort_resolver::SortResolver;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn resolve_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> ResolverOutput<'genv> {
    match try_resolve_crate(genv) {
        Ok(output) => output,
        Err(err) => genv.sess().abort(err),
    }
}

fn try_resolve_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> Result<ResolverOutput<'genv>> {
    let specs = genv.collect_specs();
    let mut resolver = CrateResolver::new(genv, specs);

    collect_flux_global_items(genv.tcx(), &mut resolver.output, specs);

    for qualifier in &specs.qualifs {
        resolver.resolve_qualifier(qualifier);
    }

    for defn in &specs.func_defs {
        resolver.resolve_defn(defn);
    }

    genv.hir().walk_toplevel_module(&mut resolver);
    if let Some(err) = resolver.err {
        return Err(err);
    }

    Ok(resolver.into_output())
}

struct CrateResolver<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    specs: &'genv Specs,
    output: ResolverOutput<'genv>,
    extern_crates: UnordMap<Symbol, CrateNum>,
    ribs: Vec<Rib>,
    err: Option<ErrorGuaranteed>,
}

#[derive(Debug, Default)]
struct Rib {
    type_ns_bindings: FxHashMap<Symbol, hir::def::Res>,
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for CrateResolver<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.genv.hir()
    }

    fn visit_mod(&mut self, module: &'tcx hir::Mod<'tcx>, _s: Span, hir_id: hir::HirId) {
        self.push_rib();
        for item_id in module.item_ids {
            let item = self.genv.hir().item(*item_id);
            let def_kind = match item.kind {
                ItemKind::Use(path, kind) => {
                    match kind {
                        hir::UseKind::Single => {
                            self.define_res_in_type_ns(
                                path.segments.last().unwrap().ident.name,
                                path.res[0],
                            );
                        }
                        hir::UseKind::Glob => {
                            let res = path.segments.last().unwrap().res;
                            let hir::def::Res::Def(DefKind::Mod, module_id) = res else {
                                continue;
                            };
                            for child in module_children(self.genv.tcx(), module_id) {
                                if child.res.ns() == Some(TypeNS) {
                                    self.define_res_in_type_ns(
                                        child.ident.name,
                                        map_res(child.res),
                                    );
                                }
                            }
                        }
                        hir::UseKind::ListStem => {}
                    }
                    continue;
                }
                ItemKind::TyAlias(..) => DefKind::TyAlias,
                ItemKind::Enum(..) => DefKind::Enum,
                ItemKind::Struct(..) => DefKind::Struct,
                ItemKind::Trait(..) => DefKind::Trait,
                ItemKind::Mod(..) => DefKind::Mod,
                _ => continue,
            };
            self.define_res_in_type_ns(
                item.ident.name,
                hir::def::Res::Def(def_kind, item.owner_id.to_def_id()),
            );
        }
        hir::intravisit::walk_mod(self, module, hir_id);
        self.pop_rib();
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        match item.kind {
            ItemKind::TyAlias(_, _) => {
                self.resolve_type_alias(item.owner_id);
            }
            ItemKind::Enum(_, _) => {
                self.resolve_enum_def(item.owner_id);
            }
            ItemKind::Struct(_, _) => {
                self.resolve_struct_def(item.owner_id);
            }
            ItemKind::Fn(..) => {
                self.resolve_fn_sig(item.owner_id);
            }
            _ => {}
        }
        hir::intravisit::walk_item(self, item);
    }

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem<'tcx>) {
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            self.resolve_fn_sig(impl_item.owner_id);
        }
        hir::intravisit::walk_impl_item(self, impl_item);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem<'tcx>) {
        if let hir::TraitItemKind::Fn(..) = trait_item.kind {
            self.resolve_fn_sig(trait_item.owner_id);
        }
        hir::intravisit::walk_trait_item(self, trait_item);
    }
}

fn module_children(tcx: TyCtxt, def_id: DefId) -> &[ModChild] {
    if let Some(local_id) = def_id.as_local() {
        tcx.module_children_local(local_id)
    } else {
        tcx.module_children(def_id)
    }
}

fn collect_flux_global_items(tcx: TyCtxt, resolver_output: &mut ResolverOutput, specs: &Specs) {
    for sort_decl in &specs.sort_decls {
        resolver_output.sort_decls.insert(
            sort_decl.name.name,
            fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span },
        );
    }

    for def_id in &specs.consts {
        let did = def_id.to_def_id();
        let sym = super::def_id_symbol(tcx, *def_id);
        resolver_output.consts.insert(sym, did);
    }

    for defn in &specs.func_defs {
        let kind = if defn.body.is_some() { fhir::FuncKind::Def } else { fhir::FuncKind::Uif };
        resolver_output.func_decls.insert(defn.name.name, kind);
    }

    for itf in flux_middle::theory_funcs() {
        resolver_output
            .func_decls
            .insert(itf.name, fhir::FuncKind::Thy(itf.fixpoint_name));
    }
}

impl<'genv, 'tcx> CrateResolver<'genv, 'tcx> {
    pub fn new(genv: GlobalEnv<'genv, 'tcx>, specs: &'genv Specs) -> Self {
        let mut extern_crates = UnordMap::default();
        for cnum in genv.tcx().crates(()) {
            let name = genv.tcx().crate_name(*cnum);
            if let Some(extern_crate) = genv.tcx().extern_crate(cnum.as_def_id())
                && extern_crate.is_direct()
            {
                extern_crates.insert(name, *cnum);
            }
        }

        Self {
            genv,
            output: ResolverOutput::default(),
            specs,
            ribs: vec![],
            extern_crates,
            err: None,
        }
    }

    fn push_rib(&mut self) {
        self.ribs.push(Rib::default());
    }

    fn define_res_in_type_ns(&mut self, name: Symbol, res: hir::def::Res) {
        self.ribs
            .last_mut()
            .unwrap()
            .type_ns_bindings
            .insert(name, res);
    }

    fn pop_rib(&mut self) {
        self.ribs.pop();
    }

    fn with_item_resolver(&mut self, owner_id: OwnerId, f: impl FnOnce(&mut ItemResolver)) {
        match ItemResolver::new(self, owner_id) {
            Ok(mut item_resolver) => f(&mut item_resolver),
            Err(err) => self.err = self.err.or(Some(err)),
        }
    }

    fn resolve_qualifier(&mut self, qualifier: &surface::Qualifier) {
        let sort_resolver = SortResolver::with_sort_params(self.genv, &self.output, &[]);
        let output = RefinementResolver::new(self.genv.tcx(), sort_resolver)
            .run(|r| r.visit_qualifier(qualifier));
        self.output
            .refinements
            .insert(fhir::FluxOwnerId::Flux(qualifier.name.name), output);
    }

    fn resolve_defn(&mut self, defn: &surface::FuncDef) {
        let sort_resolver = SortResolver::with_sort_params(self.genv, &self.output, &[]);
        let output =
            RefinementResolver::new(self.genv.tcx(), sort_resolver).run(|r| r.visit_defn(defn));
        self.output
            .refinements
            .insert(fhir::FluxOwnerId::Flux(defn.name.name), output);
    }

    fn resolve_type_alias(&mut self, owner_id: OwnerId) {
        if let Some(ty_alias) = &self.specs.ty_aliases[&owner_id] {
            self.with_item_resolver(owner_id, |item_resolver| {
                item_resolver.visit_ty_alias(ty_alias);
                let output = item_resolver
                    .as_refinement_resolver()
                    .run(|r| r.visit_ty_alias(ty_alias));
                item_resolver
                    .resolver
                    .output
                    .refinements
                    .insert(owner_id.into(), output);
            });
        };
    }

    fn resolve_struct_def(&mut self, owner_id: OwnerId) {
        let struct_def = &self.specs.structs[&owner_id];
        if !struct_def.needs_resolving() {
            return;
        }

        self.with_item_resolver(owner_id, |item_resolver| {
            item_resolver.visit_struct_def(struct_def);
            let output = item_resolver
                .as_refinement_resolver()
                .run(|r| r.visit_struct_def(struct_def));
            item_resolver
                .resolver
                .output
                .refinements
                .insert(owner_id.into(), output);
        });
    }

    fn resolve_enum_def(&mut self, owner_id: OwnerId) {
        let enum_def = &self.specs.enums[&owner_id];
        if !enum_def.needs_resolving() {
            return;
        }

        self.with_item_resolver(owner_id, |item_resolver| {
            item_resolver.visit_enum_def(enum_def);
            let output = item_resolver
                .as_refinement_resolver()
                .run(|r| r.visit_enum_def(enum_def));
            item_resolver
                .resolver
                .output
                .refinements
                .insert(owner_id.into(), output);
        });
    }

    fn resolve_fn_sig(&mut self, owner_id: OwnerId) {
        if let Some(fn_sig) = &self.specs.fn_sigs[&owner_id].fn_sig {
            self.with_item_resolver(owner_id, |item_resolver| {
                item_resolver.visit_fn_sig(fn_sig);
                item_resolver
                    .as_refinement_resolver()
                    .wrap()
                    .visit_fn_sig(fn_sig);
            });
        };
    }

    fn resolve_path(&self, path: &surface::Path) -> Option<hir::def::Res> {
        let mut module: Option<DefId> = None;
        for (i, segment) in path.segments.iter().enumerate() {
            let res = if let Some(module) = module {
                self.resolve_ident_in_module(module, *segment)?
            } else {
                self.resolve_ident(*segment)?
            };

            let hir::def::Res::Def(def_kind, res_def_id) = res else {
                return None;
            };

            match def_kind {
                DefKind::Struct | DefKind::Enum | DefKind::Trait => {
                    if i < path.segments.len() - 1 {
                        return None;
                    }
                    return Some(res);
                }
                DefKind::Mod => {
                    module = Some(res_def_id);
                }
                _ => {
                    return None;
                }
            }
        }
        None
    }

    fn resolve_ident(&self, ident: Ident) -> Option<hir::def::Res> {
        for rib in self.ribs.iter().rev() {
            if let Some(res) = rib.type_ns_bindings.get(&ident.name) {
                return Some(*res);
            }
        }
        if let Some(cnum) = self.extern_crates.get(&ident.name) {
            return Some(hir::def::Res::Def(DefKind::Mod, cnum.as_def_id()));
        }
        None
    }

    fn resolve_ident_in_module(&self, module_id: DefId, ident: Ident) -> Option<hir::def::Res> {
        module_children(self.genv.tcx(), module_id)
            .iter()
            .find_map(|child| {
                if child.vis.is_public() && child.ident == ident {
                    Some(map_res(child.res))
                } else {
                    None
                }
            })
    }

    pub fn into_output(self) -> ResolverOutput<'genv> {
        self.output
    }

    fn emit(&mut self, err: impl IntoDiagnostic<'genv>) {
        self.err = self.err.or(Some(self.genv.sess().emit_err(err)));
    }
}

struct ItemResolver<'a, 'genv, 'tcx> {
    owner_id: OwnerId,
    table: NameResTable,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
}

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct ResKey {
    s: String,
}

#[derive(Default)]
struct NameResTable {
    res: UnordMap<ResKey, ResEntry>,
    opaque: Option<ItemId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
}

#[derive(Debug, PartialEq, Eq)]
enum ResEntry {
    Res(Res),
    Unsupported { reason: String, span: Span },
}

impl<'a, 'genv, 'tcx> ItemResolver<'a, 'genv, 'tcx> {
    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>, owner_id: OwnerId) -> Result<Self> {
        let tcx = resolver.genv.tcx();
        let sess = resolver.genv.sess();
        let table = match tcx.hir().owner(owner_id) {
            hir::OwnerNode::Item(item) => NameResTable::from_item(tcx, sess, item)?,
            hir::OwnerNode::ImplItem(impl_item) => {
                NameResTable::from_impl_item(tcx, sess, impl_item)?
            }
            hir::OwnerNode::TraitItem(trait_item) => {
                NameResTable::from_trait_item(tcx, sess, trait_item)?
            }
            node @ (hir::OwnerNode::ForeignItem(_) | hir::OwnerNode::Crate(_)) => {
                bug!("unsupported node {node:?}")
            }
        };

        Ok(Self { owner_id, table, resolver })
    }

    fn resolve_opaque_impl(&mut self, node_id: surface::NodeId, span: Span) {
        if let Some(def_id) = self.table.opaque {
            self.resolver
                .output
                .impl_trait_res_map
                .insert(node_id, def_id);
        } else {
            self.resolver
                .emit(errors::UnresolvedPath { span, path: "opaque type".into() });
        }
    }

    fn resolve_path(&mut self, path: &surface::Path) {
        if let Some(res) = self.table.get(&ResKey::from_surface_path(path)) {
            match res {
                &ResEntry::Res(res) => {
                    self.resolver.output.path_res_map.insert(path.node_id, res);
                }
                ResEntry::Unsupported { reason, span } => {
                    self.resolver
                        .emit(errors::UnsupportedSignature::new(*span, reason));
                }
            }
        } else if let Some(res) = self.resolver.resolve_path(path) {
            match res.try_into() {
                Ok(res) => {
                    self.resolver.output.path_res_map.insert(path.node_id, res);
                }
                Err(_) => {
                    self.resolver
                        .emit(errors::UnsupportedSignature::new(path.span, "unsupported path"));
                }
            }
        } else {
            self.resolver.emit(errors::UnresolvedPath::new(path));
        }
    }

    fn as_refinement_resolver(&self) -> RefinementResolver<'_, 'genv, 'tcx> {
        let sort_resolver =
            SortResolver::with_generics(self.resolver.genv, &self.resolver.output, self.owner_id);
        RefinementResolver::new(self.resolver.genv.tcx(), sort_resolver)
    }
}

impl surface::visit::Visitor for ItemResolver<'_, '_, '_> {
    fn visit_async(&mut self, asyncness: &surface::Async) {
        if let surface::Async::Yes { node_id, span } = asyncness {
            self.resolve_opaque_impl(*node_id, *span);
        }
    }

    fn visit_ty(&mut self, ty: &surface::Ty) {
        match &ty.kind {
            surface::TyKind::Base(bty) => {
                // CODESYNC(type-holes, 3) we don't resolve type holes because they will be desugared
                // to `fhir::TyKind::Hole`. The path won't have an entry in `path_res_map` which we
                // should consider during desugaring. Holes in other positions (e.g., _[10] or _{v: v > 0})
                // will fail resolving so they don't show up in desugaring.
                if let BaseTyKind::Path(path) = &bty.kind
                    && path.is_hole()
                {
                    return;
                }
            }
            surface::TyKind::ImplTrait(node_id, _) => {
                self.resolve_opaque_impl(*node_id, ty.span);
            }
            _ => {}
        }
        surface::visit::walk_ty(self, ty);
    }

    fn visit_path(&mut self, path: &surface::Path) {
        self.resolve_path(path);
        surface::visit::walk_path(self, path);
    }
}

fn map_res(res: hir::def::Res<!>) -> hir::def::Res {
    match res {
        hir::def::Res::Def(k, id) => hir::def::Res::Def(k, id),
        hir::def::Res::PrimTy(pty) => hir::def::Res::PrimTy(pty),
        hir::def::Res::SelfTyParam { trait_ } => hir::def::Res::SelfTyParam { trait_ },
        hir::def::Res::SelfTyAlias { alias_to, forbid_generic, is_trait_impl } => {
            hir::def::Res::SelfTyAlias { alias_to, forbid_generic, is_trait_impl }
        }
        hir::def::Res::SelfCtor(id) => hir::def::Res::SelfCtor(id),
        hir::def::Res::ToolMod => hir::def::Res::ToolMod,
        hir::def::Res::NonMacroAttr(nma) => hir::def::Res::NonMacroAttr(nma),
        hir::def::Res::Err => hir::def::Res::Err,
        hir::def::Res::Local(_) => unreachable!(),
    }
}

struct NameResCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    table: NameResTable,
    err: Option<ErrorGuaranteed>,
}

impl<'a, 'tcx> NameResCollector<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession) -> Self {
        Self { tcx, sess, table: NameResTable::default(), err: None }
    }

    fn collect_from_opaque_impl(&mut self) -> Result {
        if let Some(item_id) = self.table.opaque {
            let item = self.tcx.hir().item(item_id);
            if let ItemKind::OpaqueTy(_) = item.kind {
                self.visit_item(item);
            }
        }
        Ok(())
    }

    fn emit(&mut self, err: impl IntoDiagnostic<'a>) {
        self.err = self.err.or(Some(self.sess.emit_err(err)));
    }

    fn into_result(self) -> Result<NameResTable> {
        if let Some(err) = self.err {
            Err(err)
        } else {
            Ok(self.table)
        }
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for NameResCollector<'_, 'tcx> {
    fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx>) {
        if let hir::TyKind::OpaqueDef(item_id, ..) = ty.kind {
            if self.table.opaque.is_some() {
                self.emit(errors::UnsupportedSignature::new(
                    ty.span,
                    "duplicate opaque types in signature",
                ));
            } else {
                self.table.opaque = Some(item_id);
            }
        }
        hir::intravisit::walk_ty(self, ty);
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _id: hir::HirId) {
        match ResKey::from_hir_path(self.sess, path) {
            Ok(key) => {
                let res = path
                    .res
                    .try_into()
                    .map_or_else(|_| ResEntry::unsupported(*path), ResEntry::Res);
                self.table.insert(key, res);
            }
            Err(err) => {
                self.err = self.err.or(Some(err));
            }
        }
        hir::intravisit::walk_path(self, path);
    }
}

impl NameResTable {
    fn from_item<'tcx>(
        tcx: TyCtxt<'tcx>,
        sess: &FluxSession,
        item: &'tcx hir::Item,
    ) -> Result<Self> {
        let def_id = item.owner_id.def_id;

        let mut collector = NameResCollector::new(tcx, sess);

        match &item.kind {
            ItemKind::Struct(variant, generics) => {
                collector.table.insert(
                    ResKey::from_ident(item.ident),
                    Res::Def(DefKind::Struct, def_id.to_def_id()),
                );
                collector.visit_generics(generics);
                collector.visit_variant_data(variant);
            }
            ItemKind::Enum(enum_def, generics) => {
                collector.table.insert(
                    ResKey::from_ident(item.ident),
                    Res::Def(DefKind::Enum, def_id.to_def_id()),
                );
                collector.visit_generics(generics);
                collector.visit_enum_def(enum_def, item.hir_id());
            }
            ItemKind::Fn(fn_sig, generics, _) => {
                collector.visit_generics(generics);
                collector.visit_fn_decl(fn_sig.decl);
                collector.collect_from_opaque_impl()?;
            }
            ItemKind::TyAlias(ty, generics) => {
                collector.visit_generics(generics);
                collector.visit_ty(ty);
            }
            _ => {}
        }
        collector.into_result()
    }

    fn from_impl_item<'tcx>(
        tcx: TyCtxt<'tcx>,
        sess: &FluxSession,
        impl_item: &'tcx hir::ImplItem,
    ) -> Result<Self> {
        let def_id = impl_item.owner_id.def_id;

        let mut collector = NameResCollector::new(tcx, sess);

        match impl_item.kind {
            hir::ImplItemKind::Fn(fn_sig, _) => {
                collector.visit_generics(impl_item.generics);
                collector.visit_fn_decl(fn_sig.decl);
            }
            hir::ImplItemKind::Const(_, _) | hir::ImplItemKind::Type(_) => {}
        }

        // Insert paths from parent impl
        let impl_did = tcx.local_parent(def_id);
        if let ItemKind::Impl(impl_) = &tcx.hir().expect_item(impl_did).kind {
            if let Some(trait_ref) = impl_.of_trait {
                let trait_id = trait_ref.trait_def_id().unwrap();
                collector.table.insert(
                    ResKey::from_hir_path(sess, trait_ref.path)?,
                    Res::Def(DefKind::Trait, trait_id),
                );
            }
            collector.visit_generics(impl_.generics);
            collector.visit_ty(impl_.self_ty);
        }

        match impl_item.kind {
            hir::ImplItemKind::Fn(fn_sig, _) => {
                collector.visit_generics(impl_item.generics);
                collector.visit_fn_decl(fn_sig.decl);
            }
            hir::ImplItemKind::Const(_, _) | hir::ImplItemKind::Type(_) => {}
        }

        collector.into_result()
    }

    fn from_trait_item<'tcx>(
        tcx: TyCtxt<'tcx>,
        sess: &FluxSession,
        trait_item: &'tcx hir::TraitItem,
    ) -> Result<Self> {
        let def_id = trait_item.owner_id.def_id;

        let mut collector = NameResCollector::new(tcx, sess);

        // Insert generics from parent trait
        if let Some(parent_impl_did) = tcx.trait_of_item(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());

            // Insert NAME of parent trait
            if let ItemKind::Trait(..) = &parent_impl_item.kind {
                collector.table.insert(
                    ResKey::from_ident(parent_impl_item.ident),
                    Res::Def(DefKind::Trait, parent_impl_did),
                );
            }

            if let ItemKind::Impl(parent) = &parent_impl_item.kind {
                collector.visit_ty(parent.self_ty);
            }
        }

        match &trait_item.kind {
            rustc_hir::TraitItemKind::Fn(fn_sig, _) => {
                collector.visit_generics(trait_item.generics);
                collector.visit_fn_decl(fn_sig.decl);
                collector.collect_from_opaque_impl()?;
            }
            rustc_hir::TraitItemKind::Const(..) | rustc_hir::TraitItemKind::Type(..) => {}
        }

        collector.into_result()
    }

    fn insert(&mut self, key: ResKey, res: impl Into<ResEntry>) {
        let res = res.into();
        match self.res.entry(key) {
            hash_map::Entry::Occupied(entry) => {
                if let ResEntry::Res(_) = res {
                    assert_eq!(entry.get(), &res);
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(res);
            }
        }
    }

    fn get(&self, key: &ResKey) -> Option<&ResEntry> {
        self.res.get(key)
    }
}

impl ResKey {
    fn from_ident(ident: Ident) -> Self {
        ResKey { s: format!("{ident}") }
    }

    fn from_surface_path(path: &surface::Path) -> ResKey {
        let s = path.segments.iter().join("::");
        ResKey { s }
    }

    fn from_hir_path(sess: &FluxSession, path: &rustc_hir::Path) -> Result<Self> {
        if let [prefix @ .., _] = path.segments
            && prefix.iter().any(|segment| segment.args.is_some())
        {
            return Err(sess.emit_err(errors::UnsupportedSignature::new(
                path.span,
                "path segments with generic arguments are not supported",
            )));
        }
        let s = path.segments.iter().map(|segment| segment.ident).join("::");
        Ok(ResKey { s })
    }
}

impl From<Res> for ResEntry {
    fn from(res: Res) -> Self {
        ResEntry::Res(res)
    }
}

impl ResEntry {
    fn unsupported(path: hir::Path) -> Self {
        Self::Unsupported { span: path.span, reason: format!("unsupported res `{:?}`", path.res) }
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use itertools::Itertools;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(desugar_unsupported_signature, code = "FLUX")]
    #[note]
    pub(super) struct UnsupportedSignature<'a> {
        #[primary_span]
        span: Span,
        note: &'a str,
    }

    impl<'a> UnsupportedSignature<'a> {
        pub(super) fn new(span: Span, note: &'a str) -> Self {
            Self { span, note }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_path, code = "FLUX")]
    #[help]
    pub struct UnresolvedPath {
        #[primary_span]
        pub span: Span,
        pub path: String,
    }

    impl UnresolvedPath {
        pub fn new(path: &surface::Path) -> Self {
            Self { span: path.span, path: path.segments.iter().join("::") }
        }
    }
}
