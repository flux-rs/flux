pub(crate) mod refinement_resolver;

use std::collections::hash_map::Entry;

use flux_common::bug;
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    fhir::{self, Res},
    global_env::GlobalEnv,
    ResolverOutput, Specs,
};
use flux_syntax::surface::{self, visit::Visitor as _, Ident, NodeId};
use hir::{
    def::{DefKind, Namespace::TypeNS},
    intravisit::Visitor as _,
    ItemId, ItemKind, OwnerId,
};
use rustc_data_structures::unord::UnordMap;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir as hir;
use rustc_middle::{metadata::ModChild, ty::TyCtxt};
use rustc_span::{
    def_id::{CrateNum, DefId},
    Span, Symbol,
};

use self::refinement_resolver::RefinementResolver;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

macro_rules! collect_err {
    ($self:expr, $body:expr) => {
        $self.err = $body.err().or($self.err)
    };
}

pub(crate) fn resolve_crate(genv: GlobalEnv) -> ResolverOutput {
    match try_resolve_crate(genv) {
        Ok(output) => output,
        Err(err) => genv.sess().abort(err),
    }
}

fn try_resolve_crate(genv: GlobalEnv) -> Result<ResolverOutput> {
    let specs = genv.collect_specs();
    let mut resolver = CrateResolver::new(genv, specs);

    resolver.collect_flux_global_items();

    for qualifier in &specs.qualifs {
        collect_err!(resolver, resolver.resolve_qualifier(qualifier));
    }

    for defn in &specs.func_defs {
        collect_err!(resolver, resolver.resolve_defn(defn));
    }

    genv.hir().walk_toplevel_module(&mut resolver);
    if let Some(err) = resolver.err {
        return Err(err);
    }

    Ok(resolver.into_output())
}

pub(crate) struct CrateResolver<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    specs: &'genv Specs,
    output: ResolverOutput,
    extern_crates: UnordMap<Symbol, CrateNum>,
    ribs: Vec<Rib>,
    func_decls: UnordMap<Symbol, fhir::SpecFuncKind>,
    sort_decls: UnordMap<Symbol, fhir::SortDecl>,
    consts: UnordMap<Symbol, DefId>,
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
            ItemKind::Trait(..) => {
                collect_err!(self, self.resolve_trait(item.owner_id));
            }
            ItemKind::Impl(..) => {
                collect_err!(self, self.resolve_impl(item.owner_id));
            }
            ItemKind::TyAlias(..) => {
                collect_err!(self, self.resolve_type_alias(item.owner_id));
            }
            ItemKind::Enum(..) => {
                collect_err!(self, self.resolve_enum_def(item.owner_id));
            }
            ItemKind::Struct(..) => {
                collect_err!(self, self.resolve_struct_def(item.owner_id));
            }
            ItemKind::Fn(..) => {
                collect_err!(self, self.resolve_fn_sig(item.owner_id));
            }
            _ => {}
        }
        hir::intravisit::walk_item(self, item);
    }

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem<'tcx>) {
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            collect_err!(self, self.resolve_fn_sig(impl_item.owner_id));
        }
        hir::intravisit::walk_impl_item(self, impl_item);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem<'tcx>) {
        if let hir::TraitItemKind::Fn(..) = trait_item.kind {
            collect_err!(self, self.resolve_fn_sig(trait_item.owner_id));
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
            func_decls: Default::default(),
            sort_decls: Default::default(),
            consts: Default::default(),
        }
    }
    fn collect_flux_global_items(&mut self) {
        for sort_decl in &self.specs.sort_decls {
            self.sort_decls.insert(
                sort_decl.name.name,
                fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span },
            );
        }

        for def_id in &self.specs.consts {
            let did = def_id.to_def_id();
            let sym = super::def_id_symbol(self.genv.tcx(), *def_id);
            self.consts.insert(sym, did);
        }

        for defn in &self.specs.func_defs {
            let kind =
                if defn.body.is_some() { fhir::SpecFuncKind::Def } else { fhir::SpecFuncKind::Uif };
            self.func_decls.insert(defn.name.name, kind);
        }

        for itf in flux_middle::theory_funcs() {
            self.func_decls
                .insert(itf.name, fhir::SpecFuncKind::Thy(itf.fixpoint_name));
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

    fn resolve_qualifier(&mut self, qualifier: &surface::Qualifier) -> Result {
        RefinementResolver::resolve_qualifier(self, qualifier)
    }

    fn resolve_defn(&mut self, defn: &surface::SpecFunc) -> Result {
        RefinementResolver::resolve_defn(self, defn)
    }

    fn resolve_trait(&mut self, owner_id: OwnerId) -> Result {
        let trait_ = &self.specs.traits[&owner_id];
        RefinementResolver::resolve_trait(self, owner_id, trait_)
    }

    fn resolve_impl(&mut self, owner_id: OwnerId) -> Result {
        let impl_ = &self.specs.impls[&owner_id];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_impl(impl_);
        })?;
        RefinementResolver::resolve_impl(self, owner_id, impl_)
    }

    fn resolve_type_alias(&mut self, owner_id: OwnerId) -> Result {
        if let Some(ty_alias) = &self.specs.ty_aliases[&owner_id] {
            ItemResolver::run(self, owner_id, |item_resolver| {
                item_resolver.visit_ty_alias(ty_alias);
            })?;
            RefinementResolver::resolve_ty_alias(self, owner_id, ty_alias)?;
        }
        Ok(())
    }

    fn resolve_struct_def(&mut self, owner_id: OwnerId) -> Result {
        let struct_def = &self.specs.structs[&owner_id];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_struct_def(struct_def);
        })?;
        RefinementResolver::resolve_struct_def(self, owner_id, struct_def)
    }

    fn resolve_enum_def(&mut self, owner_id: OwnerId) -> Result {
        let enum_def = &self.specs.enums[&owner_id];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_enum_def(enum_def);
        })?;
        RefinementResolver::resolve_enum_def(self, owner_id, enum_def)
    }

    fn resolve_fn_sig(&mut self, owner_id: OwnerId) -> Result {
        if let Some(fn_sig) = &self.specs.fn_sigs[&owner_id].fn_sig {
            ItemResolver::run(self, owner_id, |item_resolver| {
                item_resolver.visit_fn_sig(fn_sig);
            })?;
            RefinementResolver::resolve_fn_sig(self, owner_id, fn_sig)?;
        }
        Ok(())
    }

    fn try_resolve_path(&mut self, path: &surface::Path) -> Option<()> {
        let mut module: Option<DefId> = None;
        for (i, segment) in path.segments.iter().enumerate() {
            let res = if let Some(module) = module {
                self.resolve_ident_in_module(module, segment.ident)?
            } else {
                self.resolve_ident(segment.ident)?
            };

            let hir::def::Res::Def(def_kind, res_def_id) = res else {
                return None;
            };

            self.output
                .path_res_map
                .insert(segment.node_id, Res::Def(def_kind, res_def_id));

            match def_kind {
                DefKind::Struct | DefKind::Enum | DefKind::Trait => {
                    if i < path.segments.len() - 1 {
                        return None;
                    }
                }
                DefKind::Mod => {
                    module = Some(res_def_id);
                }
                _ => {
                    return None;
                }
            }
        }
        Some(())
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

    pub fn into_output(self) -> ResolverOutput {
        self.output
    }
}

struct ItemResolver<'a, 'genv, 'tcx> {
    table: NameResTable,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    opaque: Option<ItemId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
    errors: Errors<'genv>,
}

struct ResTableNode {
    res: Res,
    children: UnordMap<Symbol, ResTableNode>,
}

impl ResTableNode {
    fn new(res: Res) -> Self {
        Self { res, children: Default::default() }
    }
}

#[derive(Default)]
struct NameResTable {
    nodes: UnordMap<Symbol, ResTableNode>,
}

impl NameResTable {
    fn insert_ident(&mut self, ident: Ident, res: Res) {
        self.nodes
            .entry(ident.name)
            .or_insert_with(|| ResTableNode::new(res));
    }

    fn insert_hir_path(&mut self, path: &hir::Path) {
        let mut nodes = &mut self.nodes;
        for segment in path.segments {
            let node = match nodes.entry(segment.ident.name) {
                Entry::Occupied(entry) => entry.into_mut(),
                Entry::Vacant(entry) => {
                    let Ok(res) = Res::try_from(segment.res) else { return };
                    entry.insert(ResTableNode::new(res))
                }
            };
            nodes = &mut node.children;
        }
    }

    fn visit_path(&self, path: &surface::Path, mut f: impl FnMut(NodeId, Res)) -> bool {
        let mut nodes = &self.nodes;
        for segment in &path.segments {
            let Some(node) = nodes.get(&segment.ident.name) else { return false };
            f(segment.node_id, node.res);
            nodes = &node.children;
        }
        true
    }
}

impl<'a, 'genv, 'tcx> ItemResolver<'a, 'genv, 'tcx> {
    fn run(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        f: impl FnOnce(&mut ItemResolver),
    ) -> Result {
        let mut item_resolver = ItemResolver::new(resolver, owner_id)?;
        f(&mut item_resolver);
        item_resolver.errors.into_result()
    }

    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>, owner_id: OwnerId) -> Result<Self> {
        let tcx = resolver.genv.tcx();
        let sess = resolver.genv.sess();
        let (table, opaque) = match tcx.hir_owner_node(owner_id) {
            hir::OwnerNode::Item(item) => NameResCollector::collect_item(tcx, sess, item)?,
            hir::OwnerNode::ImplItem(impl_item) => {
                NameResCollector::collect_impl_item(tcx, sess, impl_item)?
            }
            hir::OwnerNode::TraitItem(trait_item) => {
                NameResCollector::collect_trait_item(tcx, sess, trait_item)?
            }
            node @ (hir::OwnerNode::ForeignItem(_)
            | hir::OwnerNode::Crate(_)
            | hir::OwnerNode::Synthetic) => {
                bug!("unsupported node {node:?}")
            }
        };

        let errors = Errors::new(resolver.genv.sess());
        Ok(Self { table, resolver, opaque, errors })
    }

    fn resolve_opaque_impl(&mut self, node_id: surface::NodeId, span: Span) {
        if let Some(def_id) = self.opaque {
            self.resolver
                .output
                .impl_trait_res_map
                .insert(node_id, def_id);
        } else {
            self.errors
                .emit(errors::UnresolvedPath { span, path: "opaque type".into() });
        }
    }

    fn resolve_path(&mut self, path: &surface::Path) {
        // This could insert stuff in `path_res_map` twice if table resolution fails midway. This
        // is ok because we will only proceed to further stages if the entire path is resolved.
        if self.try_resolve_with_table(path) {
            return;
        }
        if self.resolver.try_resolve_path(path).is_some() {
            return;
        }
        self.errors.emit(errors::UnresolvedPath::new(path));
    }

    fn try_resolve_with_table(&mut self, path: &surface::Path) -> bool {
        self.table.visit_path(path, |segment_id, res| {
            self.resolver.output.path_res_map.insert(segment_id, res);
        })
    }
}

impl surface::visit::Visitor for ItemResolver<'_, '_, '_> {
    fn visit_async(&mut self, asyncness: &surface::Async) {
        if let surface::Async::Yes { node_id, span } = asyncness {
            self.resolve_opaque_impl(*node_id, *span);
        }
    }

    fn visit_ty(&mut self, ty: &surface::Ty) {
        if let surface::TyKind::ImplTrait(node_id, _) = &ty.kind {
            self.resolve_opaque_impl(*node_id, ty.span);
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

struct NameResCollector<'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    table: NameResTable,
    opaque: Option<ItemId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
    errors: Errors<'sess>,
}

impl<'sess, 'tcx> NameResCollector<'sess, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sess: &'sess FluxSession) -> Self {
        Self { tcx, table: NameResTable::default(), opaque: None, errors: Errors::new(sess) }
    }

    fn collect_item(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        item: &'tcx hir::Item,
    ) -> Result<(NameResTable, Option<ItemId>)> {
        let def_id = item.owner_id.def_id;

        let mut collector = Self::new(tcx, sess);

        match &item.kind {
            ItemKind::Struct(variant, generics) => {
                collector
                    .table
                    .insert_ident(item.ident, Res::Def(DefKind::Struct, def_id.to_def_id()));
                collector.visit_generics(generics);
                collector.visit_variant_data(variant);
            }
            ItemKind::Enum(enum_def, generics) => {
                collector
                    .table
                    .insert_ident(item.ident, Res::Def(DefKind::Enum, def_id.to_def_id()));
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
            ItemKind::Impl(impl_) => {
                collector.visit_generics(impl_.generics);
                collector.visit_ty(impl_.self_ty);
            }
            _ => {}
        }
        collector.into_result()
    }

    fn collect_impl_item(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        impl_item: &'tcx hir::ImplItem,
    ) -> Result<(NameResTable, Option<ItemId>)> {
        let def_id = impl_item.owner_id.def_id;

        let mut collector = Self::new(tcx, sess);

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
                collector.table.insert_hir_path(trait_ref.path);
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

    fn collect_trait_item(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        trait_item: &'tcx hir::TraitItem,
    ) -> Result<(NameResTable, Option<ItemId>)> {
        let def_id = trait_item.owner_id.def_id;

        let mut collector = Self::new(tcx, sess);

        // Insert generics from parent trait
        if let Some(parent_impl_did) = tcx.trait_of_item(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());

            // Insert NAME of parent trait
            if let ItemKind::Trait(..) = &parent_impl_item.kind {
                collector.table.insert_ident(
                    parent_impl_item.ident,
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

    fn collect_from_opaque_impl(&mut self) -> Result {
        if let Some(item_id) = self.opaque {
            let item = self.tcx.hir().item(item_id);
            if let ItemKind::OpaqueTy(_) = item.kind {
                self.visit_item(item);
            }
        }
        Ok(())
    }

    fn into_result(self) -> Result<(NameResTable, Option<ItemId>)> {
        self.errors.into_result()?;
        Ok((self.table, self.opaque))
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for NameResCollector<'_, 'tcx> {
    fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx>) {
        if let hir::TyKind::OpaqueDef(item_id, ..) = ty.kind {
            if self.opaque.is_some() {
                self.errors.emit(errors::UnsupportedSignature::new(
                    ty.span,
                    "duplicate opaque types in signature",
                ));
            } else {
                self.opaque = Some(item_id);
            }
        }
        hir::intravisit::walk_ty(self, ty);
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _id: hir::HirId) {
        self.table.insert_hir_path(path);
        hir::intravisit::walk_path(self, path);
    }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use itertools::Itertools;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(desugar_unsupported_signature, code = E0999)]
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
    #[diag(desugar_unresolved_path, code = E0999)]
    #[help]
    pub struct UnresolvedPath {
        #[primary_span]
        pub span: Span,
        pub path: String,
    }

    impl UnresolvedPath {
        pub fn new(path: &surface::Path) -> Self {
            Self {
                span: path.span,
                path: path.segments.iter().map(|segment| segment.ident).join("::"),
            }
        }
    }
}
