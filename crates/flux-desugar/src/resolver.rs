use std::collections::hash_map;

use flux_common::{bug, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, Res},
    Specs,
};
use flux_syntax::surface::{self, visit::Visitor, BaseTyKind, Ident, Path, Ty};
use hir::{
    def::{DefKind, Namespace::TypeNS},
    ItemId, ItemKind, OwnerId, PathSegment,
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

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn resolve_crate(
    tcx: TyCtxt,
    sess: &FluxSession,
    specs: &Specs,
) -> Result<ResolverOutput> {
    let mut resolver = CrateResolver::new(tcx, sess, specs);

    tcx.hir().walk_toplevel_module(&mut resolver);
    if let Some(err) = resolver.err {
        return Err(err);
    }
    let mut resolver_output = resolver.into_output();

    collect_flux_global_items(tcx, &mut resolver_output, specs);

    Ok(resolver_output)
}

struct CrateResolver<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    specs: &'a Specs,
    output: ResolverOutput,
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
        self.tcx.hir()
    }

    fn visit_mod(&mut self, module: &'tcx hir::Mod<'tcx>, _s: Span, hir_id: hir::HirId) {
        self.push_rib();
        for item_id in module.item_ids {
            let item = self.tcx.hir().item(*item_id);
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
                            for child in module_children(self.tcx, module_id) {
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

#[derive(Default)]
pub(crate) struct ResolverOutput {
    pub path_res_map: UnordMap<surface::NodeId, Res>,
    pub impl_trait_res_map: UnordMap<surface::NodeId, ItemId>,
    pub func_decls: UnordMap<Symbol, fhir::FuncKind>,
    pub sort_decls: UnordMap<Symbol, fhir::SortDecl>,
    pub consts: UnordMap<Symbol, DefId>,
}

fn collect_flux_global_items(tcx: TyCtxt, resolver_output: &mut ResolverOutput, specs: &Specs) {
    for sort_decl in &specs.sort_decls {
        resolver_output.sort_decls.insert(
            sort_decl.name.name,
            fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span },
        );
    }

    for def_id in specs.consts.keys() {
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

impl<'a, 'tcx> CrateResolver<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession, specs: &'a Specs) -> Self {
        let mut extern_crates = UnordMap::default();
        for cnum in tcx.crates(()) {
            let name = tcx.crate_name(*cnum);
            if let Some(extern_crate) = tcx.extern_crate(cnum.as_def_id())
                && extern_crate.is_direct()
            {
                extern_crates.insert(name, *cnum);
            }
        }

        Self {
            tcx,
            sess,
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

    fn resolve_type_alias(&mut self, owner_id: OwnerId) {
        if let Some(ty_alias) = &self.specs.ty_aliases[&owner_id] {
            self.with_item_resolver(owner_id, |item_resolver| {
                item_resolver.visit_ty_alias(ty_alias);
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
        });
    }

    fn resolve_enum_def(&mut self, owner_id: OwnerId) {
        let enum_def = &self.specs.enums[&owner_id];
        if !enum_def.needs_resolving() {
            return;
        }

        self.with_item_resolver(owner_id, |item_resolver| {
            item_resolver.visit_enum_def(enum_def);
        });
    }

    fn resolve_fn_sig(&mut self, owner_id: OwnerId) {
        if let Some(fn_sig) = &self.specs.fn_sigs[&owner_id].fn_sig {
            self.with_item_resolver(owner_id, |item_resolver| {
                item_resolver.visit_fn_sig(fn_sig);
            });
        };
    }

    fn resolve_path(&self, path: &Path) -> Option<hir::def::Res> {
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
        module_children(self.tcx, module_id)
            .iter()
            .find_map(|child| {
                if child.vis.is_public() && child.ident == ident {
                    Some(map_res(child.res))
                } else {
                    None
                }
            })
    }

    pub fn into_output(self) -> ResolverOutput {
        self.output
    }

    fn emit(&mut self, err: impl IntoDiagnostic<'a>) {
        self.err = self.err.or(Some(self.sess.emit_err(err)));
    }
}

struct ItemResolver<'a, 'b, 'tcx> {
    table: NameResTable<'a>,
    resolver: &'a mut CrateResolver<'b, 'tcx>,
}

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct ResKey {
    s: String,
}

struct NameResTable<'sess> {
    res: UnordMap<ResKey, ResEntry>,
    opaque: Option<ItemId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
    sess: &'sess FluxSession,
}

#[derive(Debug, PartialEq, Eq)]
enum ResEntry {
    Res(Res),
    Unsupported { reason: String, span: Span },
}

impl<'a, 'b, 'tcx> ItemResolver<'a, 'b, 'tcx> {
    fn new(resolver: &'a mut CrateResolver<'b, 'tcx>, owner_id: OwnerId) -> Result<Self> {
        let tcx = resolver.tcx;
        let sess = resolver.sess;
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

        Ok(Self { table, resolver })
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

    fn resolve_path(&mut self, path: &Path) {
        if let Some(res) = self.table.get(&ResKey::from_path(path)) {
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
}

impl surface::visit::Visitor for ItemResolver<'_, '_, '_> {
    fn visit_async(&mut self, asyncness: &surface::Async) {
        if let surface::Async::Yes { node_id, span } = asyncness {
            self.resolve_opaque_impl(*node_id, *span);
        }
    }

    fn visit_ty(&mut self, ty: &Ty) {
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

    fn visit_path(&mut self, path: &Path) {
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

impl<'sess> NameResTable<'sess> {
    fn new(sess: &'sess FluxSession) -> NameResTable<'sess> {
        NameResTable { sess, opaque: None, res: UnordMap::default() }
    }

    fn from_item(tcx: TyCtxt, sess: &'sess FluxSession, item: &hir::Item) -> Result<Self> {
        let mut table = Self::new(sess);
        let def_id = item.owner_id.def_id;
        match &item.kind {
            ItemKind::TyAlias(ty, _) => {
                table.collect_from_ty(ty)?;
            }
            ItemKind::Struct(data, _) => {
                table.insert(
                    ResKey::from_ident(item.ident),
                    Res::Def(DefKind::Struct, def_id.to_def_id()),
                );

                for field in data.fields() {
                    table.collect_from_ty(field.ty)?;
                }
            }
            ItemKind::Enum(data, _) => {
                table.insert(
                    ResKey::from_ident(item.ident),
                    Res::Def(DefKind::Enum, def_id.to_def_id()),
                );

                for variant in data.variants {
                    for field in variant.data.fields() {
                        table.collect_from_ty(field.ty)?;
                    }
                }
            }
            ItemKind::Fn(fn_sig, generics, ..) => {
                table.collect_from_fn_sig(fn_sig)?;
                table.collect_from_generics(generics)?;
                table.collect_from_opaque_impls(tcx)?;
            }
            _ => {}
        }
        Ok(table)
    }

    fn from_impl_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        impl_item: &hir::ImplItem,
    ) -> Result<Self> {
        let def_id = impl_item.owner_id.def_id;

        let mut table = Self::new(sess);

        table.collect_from_generics(impl_item.generics)?;

        // Insert paths from parent impl
        let impl_did = tcx.local_parent(def_id);
        if let ItemKind::Impl(impl_) = &tcx.hir().expect_item(impl_did).kind {
            if let Some(trait_ref) = impl_.of_trait {
                let trait_id = trait_ref.trait_def_id().unwrap();
                table.insert(
                    ResKey::from_hir_path(sess, trait_ref.path)?,
                    Res::Def(DefKind::Trait, trait_id),
                );
            }
            table.collect_from_generics(impl_.generics)?;
            table.collect_from_ty(impl_.self_ty)?;
        }

        match &impl_item.kind {
            rustc_hir::ImplItemKind::Fn(fn_sig, _) => {
                table.collect_from_fn_sig(fn_sig)?;
                table.collect_from_opaque_impls(tcx)?;
            }
            rustc_hir::ImplItemKind::Const(_, _) | rustc_hir::ImplItemKind::Type(_) => {}
        }

        Ok(table)
    }

    fn from_trait_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        trait_item: &hir::TraitItem,
    ) -> Result<Self> {
        let def_id = trait_item.owner_id.def_id;

        let mut table = Self::new(sess);

        // Insert generics from parent trait
        if let Some(parent_impl_did) = tcx.trait_of_item(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());

            // Insert NAME of parent trait
            if let ItemKind::Trait(..) = &parent_impl_item.kind {
                table.insert(
                    ResKey::from_ident(parent_impl_item.ident),
                    Res::Def(DefKind::Trait, parent_impl_did),
                );
            }

            if let ItemKind::Impl(parent) = &parent_impl_item.kind {
                table.collect_from_ty(parent.self_ty)?;
            }
        }

        match &trait_item.kind {
            rustc_hir::TraitItemKind::Fn(fn_sig, _) => {
                table.collect_from_fn_sig(fn_sig)?;
                table.collect_from_opaque_impls(tcx)?;
            }
            rustc_hir::TraitItemKind::Const(..) | rustc_hir::TraitItemKind::Type(..) => {}
        }

        Ok(table)
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

    fn collect_from_generics(&mut self, generics: &hir::Generics<'_>) -> Result {
        generics
            .predicates
            .iter()
            .try_for_each_exhaust(|pred| self.collect_from_where_predicate(pred))
    }

    fn collect_from_where_predicate(&mut self, clause: &hir::WherePredicate) -> Result {
        if let hir::WherePredicate::BoundPredicate(bound) = clause {
            self.collect_from_ty(bound.bounded_ty)?;
            self.collect_from_generic_bounds(bound.bounds)?;
        }
        Ok(())
    }

    fn collect_from_generic_bounds(&mut self, bounds: &[hir::GenericBound<'_>]) -> Result {
        bounds
            .iter()
            .try_for_each_exhaust(|b| self.collect_from_generic_bound(b))?;
        Ok(())
    }

    fn collect_from_generic_bound(&mut self, bound: &hir::GenericBound) -> Result {
        match bound {
            hir::GenericBound::Trait(poly_trait_ref, _) => {
                self.collect_from_path(poly_trait_ref.trait_ref.path)
            }
            hir::GenericBound::LangItemTrait(.., args) => self.collect_from_generic_args(args),
            _ => Ok(()),
        }
    }

    fn collect_from_opaque_impls(&mut self, tcx: TyCtxt) -> Result {
        if let Some(item_id) = self.opaque {
            let item_kind = tcx.hir().item(item_id).kind;
            if let ItemKind::OpaqueTy(opaque_ty) = item_kind {
                self.collect_from_generic_bounds(opaque_ty.bounds)?;
            }
        }
        Ok(())
    }

    fn collect_from_fn_sig(&mut self, fn_sig: &hir::FnSig) -> Result {
        fn_sig
            .decl
            .inputs
            .iter()
            .try_for_each_exhaust(|ty| self.collect_from_ty(ty))?;

        if let hir::FnRetTy::Return(ty) = fn_sig.decl.output {
            self.collect_from_ty(ty)?;
        }
        Ok(())
    }

    fn collect_from_ty(&mut self, ty: &hir::Ty) -> Result {
        match &ty.kind {
            hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => self.collect_from_ty(ty),
            hir::TyKind::Ptr(mut_ty) | hir::TyKind::Ref(_, mut_ty) => {
                self.collect_from_ty(mut_ty.ty)
            }
            hir::TyKind::Tup(tys) => tys.iter().try_for_each(|ty| self.collect_from_ty(ty)),
            hir::TyKind::Path(qpath) => {
                match qpath {
                    hir::QPath::Resolved(self_ty, path) => {
                        self.collect_from_path(path)?;
                        if let Some(self_ty) = self_ty {
                            self.collect_from_ty(self_ty)?;
                        }
                    }
                    hir::QPath::TypeRelative(ty, _path_segment) => {
                        self.collect_from_ty(ty)?;
                    }
                    hir::QPath::LangItem(..) => {}
                }
                Ok(())
            }
            hir::TyKind::OpaqueDef(item_id, ..) => {
                assert!(self.opaque.is_none());
                if self.opaque.is_some() {
                    Err(self.sess.emit_err(errors::UnsupportedSignature::new(
                        ty.span,
                        "duplicate opaque types in signature",
                    )))
                } else {
                    self.opaque = Some(*item_id);
                    Ok(())
                }
            }
            hir::TyKind::BareFn(_)
            | hir::TyKind::Never
            | hir::TyKind::TraitObject(..)
            | hir::TyKind::Typeof(_)
            | hir::TyKind::Infer
            | hir::TyKind::Err(_) => Ok(()),
        }
    }

    fn collect_from_generic_args(&mut self, args: &rustc_hir::GenericArgs) -> Result {
        args.args
            .iter()
            .copied()
            .try_for_each_exhaust(|arg| self.collect_from_generic_arg(&arg))?;

        args.bindings
            .iter()
            .copied()
            .try_for_each_exhaust(|binding| self.collect_from_type_binding(&binding))?;
        Ok(())
    }

    fn collect_from_path(&mut self, path: &hir::Path<'_>) -> Result {
        let key = ResKey::from_hir_path(self.sess, path)?;

        let res = path
            .res
            .try_into()
            .map_or_else(|_| ResEntry::unsupported(*path), ResEntry::Res);
        self.insert(key, res);

        if let [.., PathSegment { args: Some(args), .. }] = path.segments {
            self.collect_from_generic_args(args)?;
        }
        Ok(())
    }

    fn collect_from_type_binding(&mut self, binding: &hir::TypeBinding<'_>) -> Result {
        match binding.kind {
            hir::TypeBindingKind::Equality { term } => self.collect_from_term(&term),
            hir::TypeBindingKind::Constraint { bounds } => {
                bounds
                    .iter()
                    .try_for_each_exhaust(|bound| self.collect_from_generic_bound(bound))
            }
        }
    }

    fn collect_from_term(&mut self, term: &hir::Term<'_>) -> Result {
        match term {
            hir::Term::Ty(ty) => self.collect_from_ty(ty),
            hir::Term::Const(_) => Ok(()),
        }
    }

    fn collect_from_generic_arg(&mut self, arg: &hir::GenericArg) -> Result {
        match arg {
            hir::GenericArg::Type(ty) => self.collect_from_ty(ty),
            hir::GenericArg::Lifetime(_) => Ok(()),
            hir::GenericArg::Const(_) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature::new(
                    arg.span(),
                    "const generics are not supported yet",
                )))
            }

            hir::GenericArg::Infer(_) => unreachable!(),
        }
    }
}

impl ResKey {
    fn from_ident(ident: Ident) -> Self {
        ResKey { s: format!("{ident}") }
    }

    fn from_path(path: &Path) -> ResKey {
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
