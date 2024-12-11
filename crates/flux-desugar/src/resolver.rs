pub(crate) mod refinement_resolver;

use flux_common::{
    bug,
    result::{ErrorCollector, ResultExt},
};
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    fhir::{self, Res},
    global_env::GlobalEnv,
    MaybeExternId, ResolverOutput, Specs,
};
use flux_syntax::surface::{self, visit::Visitor as _, Ident};
use hir::{def::DefKind, ItemId, ItemKind, OwnerId};
use rustc_data_structures::unord::{ExtendUnord, UnordMap};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{
    self as hir,
    def::{
        Namespace::{self, *},
        PerNS,
    },
    def_id::{LocalDefId, CRATE_DEF_ID},
    ParamName, PrimTy, CRATE_HIR_ID, CRATE_OWNER_ID,
};
use rustc_middle::{metadata::ModChild, ty::TyCtxt};
use rustc_span::{def_id::DefId, sym, symbol::kw, Span, Symbol};

use self::refinement_resolver::RefinementResolver;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn resolve_crate(genv: GlobalEnv) -> ResolverOutput {
    match try_resolve_crate(genv) {
        Ok(output) => output,
        Err(err) => genv.sess().abort(err),
    }
}

fn try_resolve_crate(genv: GlobalEnv) -> Result<ResolverOutput> {
    let specs = genv.collect_specs();
    let mut resolver = CrateResolver::new(genv, specs);

    genv.hir().walk_toplevel_module(&mut resolver);

    resolver.into_output()
}

pub(crate) struct CrateResolver<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    specs: &'genv Specs,
    output: ResolverOutput,
    ribs: PerNS<Vec<Rib>>,
    /// A mapping from the names of all imported crates plus the special `crate` keyword to their
    /// [`DefId`]
    crates: UnordMap<Symbol, DefId>,
    prelude: PerNS<Rib>,
    func_decls: UnordMap<Symbol, fhir::SpecFuncKind>,
    sort_decls: UnordMap<Symbol, fhir::SortDecl>,
    err: Option<ErrorGuaranteed>,
    /// The most recent module we have visited. Used to check for visibility of other items from
    /// this module.
    current_module: OwnerId,
}

impl<'genv, 'tcx> CrateResolver<'genv, 'tcx> {
    pub fn new(genv: GlobalEnv<'genv, 'tcx>, specs: &'genv Specs) -> Self {
        Self {
            genv,
            output: ResolverOutput::default(),
            specs,
            ribs: PerNS { type_ns: vec![], value_ns: vec![], macro_ns: vec![] },
            crates: mk_crate_mapping(genv.tcx()),
            prelude: PerNS {
                type_ns: builtin_types_rib(),
                value_ns: Rib::new(RibKind::Normal),
                macro_ns: Rib::new(RibKind::Normal),
            },
            err: None,
            func_decls: Default::default(),
            sort_decls: Default::default(),
            current_module: CRATE_OWNER_ID,
        }
    }

    fn define_flux_global_items(&mut self) {
        for item in self.specs.flux_items_by_parent.values().flatten() {
            match item {
                surface::Item::Qualifier(_) => {}
                surface::Item::FuncDef(defn) => {
                    let kind = if defn.body.is_some() {
                        fhir::SpecFuncKind::Def
                    } else {
                        fhir::SpecFuncKind::Uif
                    };
                    self.func_decls.insert(defn.name.name, kind);
                }
                surface::Item::SortDecl(sort_decl) => {
                    self.sort_decls.insert(
                        sort_decl.name.name,
                        fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span },
                    );
                }
            }
        }

        self.func_decls.extend_unord(
            flux_middle::THEORY_FUNCS
                .items()
                .map(|(name, itf)| (*name, fhir::SpecFuncKind::Thy(itf.fixpoint_name))),
        );
    }

    fn define_items(&mut self, item_ids: impl IntoIterator<Item = &'tcx ItemId>) {
        for item_id in item_ids {
            let item = self.genv.hir().item(*item_id);
            let def_kind = match item.kind {
                ItemKind::Use(path, kind) => {
                    match kind {
                        hir::UseKind::Single => {
                            let name = path.segments.last().unwrap().ident.name;
                            for res in &path.res {
                                if let Some(ns @ (TypeNS | ValueNS)) = res.ns() {
                                    self.define_res_in(name, *res, ns);
                                }
                            }
                        }
                        hir::UseKind::Glob => {
                            let is_prelude = is_prelude_import(self.genv.tcx(), item);
                            for mod_child in glob_imports(self.genv.tcx(), path) {
                                if let Some(ns @ (TypeNS | ValueNS)) = mod_child.res.ns() {
                                    let name = mod_child.ident.name;
                                    let res = map_res(mod_child.res);
                                    if is_prelude {
                                        self.define_in_prelude(name, res, ns);
                                    } else {
                                        self.define_res_in(name, res, ns);
                                    }
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
                ItemKind::Const(..) => DefKind::Const,
                _ => continue,
            };
            if let Some(ns) = def_kind.ns() {
                self.define_res_in(
                    item.ident.name,
                    hir::def::Res::Def(def_kind, item.owner_id.to_def_id()),
                    ns,
                );
            }
        }
    }

    fn define_res_in(&mut self, name: Symbol, res: hir::def::Res, ns: Namespace) {
        self.ribs[ns].last_mut().unwrap().bindings.insert(name, res);
    }

    fn define_in_prelude(&mut self, name: Symbol, res: hir::def::Res, ns: Namespace) {
        self.prelude[ns].bindings.insert(name, res);
    }

    fn push_rib(&mut self, ns: Namespace, kind: RibKind) {
        self.ribs[ns].push(Rib::new(kind));
    }

    fn pop_rib(&mut self, ns: Namespace) {
        self.ribs[ns].pop();
    }

    fn define_generics(&mut self, def_id: MaybeExternId<OwnerId>) {
        let generics = self
            .genv
            .hir()
            .get_generics(def_id.local_id().def_id)
            .unwrap();
        for param in generics.params {
            let def_kind = self.genv.tcx().def_kind(param.def_id);
            if let ParamName::Plain(name) = param.name
                && let Some(ns) = def_kind.ns()
            {
                debug_assert!(matches!(def_kind, DefKind::TyParam | DefKind::ConstParam));
                let param_id = self.genv.maybe_extern_id(param.def_id).resolved_id();
                self.define_res_in(name.name, hir::def::Res::Def(def_kind, param_id), ns);
            }
        }
    }

    fn resolve_flux_items(&mut self, parent: OwnerId) {
        let Some(items) = self.specs.flux_items_by_parent.get(&parent) else { return };
        for item in items {
            match item {
                surface::Item::Qualifier(qual) => {
                    RefinementResolver::resolve_qualifier(self, qual).collect_err(&mut self.err);
                }
                surface::Item::FuncDef(defn) => {
                    RefinementResolver::resolve_defn(self, defn).collect_err(&mut self.err);
                }
                surface::Item::SortDecl(_) => {}
            }
        }
    }

    fn resolve_trait(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        let trait_ = &self.specs.traits[&owner_id.local_id()];
        RefinementResolver::resolve_trait(self, trait_)
    }

    fn resolve_impl(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        let impl_ = &self.specs.impls[&owner_id.local_id()];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_impl(impl_);
        })?;
        RefinementResolver::resolve_impl(self, impl_)
    }

    fn resolve_type_alias(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        if let Some(ty_alias) = &self.specs.ty_aliases[&owner_id.local_id()] {
            ItemResolver::run(self, owner_id, |item_resolver| {
                item_resolver.visit_ty_alias(ty_alias);
            })?;
            RefinementResolver::resolve_ty_alias(self, ty_alias)?;
        }
        Ok(())
    }

    fn resolve_struct_def(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        let struct_def = &self.specs.structs[&owner_id.local_id()];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_struct_def(struct_def);
        })?;
        RefinementResolver::resolve_struct_def(self, struct_def)
    }

    fn resolve_enum_def(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        let enum_def = &self.specs.enums[&owner_id.local_id()];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_enum_def(enum_def);
        })?;
        RefinementResolver::resolve_enum_def(self, enum_def)
    }

    fn resolve_constant(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        let constant = &self.specs.constants[&owner_id.local_id()];
        ItemResolver::run(self, owner_id, |item_resolver| {
            item_resolver.visit_constant(constant);
        })?;
        RefinementResolver::resolve_constant(self, constant)
    }
    
    fn resolve_fn_sig(&mut self, owner_id: MaybeExternId<OwnerId>) -> Result {
        if let Some(fn_sig) = &self.specs.fn_sigs[&owner_id.local_id()].fn_sig {
            ItemResolver::run(self, owner_id, |item_resolver| {
                item_resolver.visit_fn_sig(fn_sig);
            })?;
            RefinementResolver::resolve_fn_sig(self, fn_sig)?;
        }
        Ok(())
    }

    fn resolve_path_with_ribs<S: Segment>(
        &mut self,
        segments: &[S],
        ns: Namespace,
    ) -> Option<fhir::PartialRes> {
        let mut module: Option<DefId> = None;

        for (segment_idx, segment) in segments.iter().enumerate() {
            let is_last = segment_idx + 1 == segments.len();
            let ns = if is_last { ns } else { TypeNS };

            let res = if let Some(module) = module {
                self.resolve_ident_in_module(module, segment.ident())?
            } else {
                self.resolve_ident_with_ribs(segment.ident(), ns)?
            };

            let base_res = Res::try_from(res).ok()?;

            S::record_segment_res(self, segment, base_res);

            if let Res::Def(DefKind::Mod, module_id) = base_res {
                module = Some(module_id);
            } else {
                return Some(fhir::PartialRes::with_unresolved_segments(
                    base_res,
                    segments.len() - segment_idx - 1,
                ));
            }
        }
        None
    }

    fn resolve_ident_with_ribs(&self, ident: Ident, ns: Namespace) -> Option<hir::def::Res> {
        for rib in self.ribs[ns].iter().rev() {
            if let Some(res) = rib.bindings.get(&ident.name) {
                return Some(*res);
            }
            if matches!(rib.kind, RibKind::Module) {
                break;
            }
        }
        if ns == TypeNS {
            if let Some(crate_id) = self.crates.get(&ident.name) {
                return Some(hir::def::Res::Def(DefKind::Mod, *crate_id));
            }
        }
        if let Some(res) = self.prelude[ns].bindings.get(&ident.name) {
            return Some(*res);
        }
        None
    }

    fn resolve_ident_in_module(&self, module_id: DefId, ident: Ident) -> Option<hir::def::Res> {
        let curr_mod = self.current_module.def_id;
        module_children(self.genv.tcx(), module_id)
            .iter()
            .find_map(|child| {
                if child.vis.is_accessible_from(curr_mod, self.genv.tcx()) && child.ident == ident {
                    Some(map_res(child.res))
                } else {
                    None
                }
            })
    }

    pub fn into_output(self) -> Result<ResolverOutput> {
        self.err.into_result()?;
        Ok(self.output)
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for CrateResolver<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.genv.hir()
    }

    fn visit_mod(&mut self, module: &'tcx hir::Mod<'tcx>, _s: Span, hir_id: hir::HirId) {
        let old_mod = self.current_module;
        self.current_module = hir_id.expect_owner();
        self.push_rib(TypeNS, RibKind::Module);
        self.push_rib(ValueNS, RibKind::Module);

        self.define_items(module.item_ids);

        // Flux items are made globally available as if they were defined at the top of the crate
        if hir_id == CRATE_HIR_ID {
            self.define_flux_global_items();
        }

        // But we resolve names in them as if they were defined in their containing module
        self.resolve_flux_items(hir_id.expect_owner());

        hir::intravisit::walk_mod(self, module, hir_id);

        self.pop_rib(ValueNS);
        self.pop_rib(TypeNS);
        self.current_module = old_mod;
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        self.push_rib(TypeNS, RibKind::Normal);
        self.push_rib(ValueNS, RibKind::Normal);

        let item_ids = block.stmts.iter().filter_map(|stmt| {
            if let hir::StmtKind::Item(item_id) = &stmt.kind {
                Some(item_id)
            } else {
                None
            }
        });
        self.define_items(item_ids);
        self.resolve_flux_items(self.genv.hir().get_parent_item(block.hir_id));

        hir::intravisit::walk_block(self, block);

        self.pop_rib(ValueNS);
        self.pop_rib(TypeNS);
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if self.genv.is_dummy(item.owner_id.def_id) {
            return;
        }
        let def_id = self
            .genv
            .maybe_extern_id(item.owner_id.def_id)
            .map(|def_id| OwnerId { def_id });

        self.push_rib(TypeNS, RibKind::Normal);
        self.push_rib(ValueNS, RibKind::Normal);

        match item.kind {
            ItemKind::Trait(..) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    hir::def::Res::SelfTyParam { trait_: def_id.resolved_id() },
                    TypeNS,
                );
                self.resolve_trait(def_id).collect_err(&mut self.err);
            }
            ItemKind::Impl(impl_) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    hir::def::Res::SelfTyAlias {
                        alias_to: def_id.resolved_id(),
                        forbid_generic: false,
                        is_trait_impl: impl_.of_trait.is_some(),
                    },
                    TypeNS,
                );
                self.resolve_impl(def_id).collect_err(&mut self.err);
            }
            ItemKind::TyAlias(..) => {
                self.define_generics(def_id);
                self.resolve_type_alias(def_id).collect_err(&mut self.err);
            }
            ItemKind::Enum(..) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    hir::def::Res::SelfTyAlias {
                        alias_to: def_id.resolved_id(),
                        forbid_generic: false,
                        is_trait_impl: false,
                    },
                    TypeNS,
                );
                self.resolve_enum_def(def_id).collect_err(&mut self.err);
            }
            ItemKind::Struct(..) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    hir::def::Res::SelfTyAlias {
                        alias_to: def_id.resolved_id(),
                        forbid_generic: false,
                        is_trait_impl: false,
                    },
                    TypeNS,
                );
                self.resolve_struct_def(def_id).collect_err(&mut self.err);
            }
            ItemKind::Fn(..) => {
                self.define_generics(def_id);
                self.resolve_fn_sig(def_id).collect_err(&mut self.err);
            }
            ItemKind::Const(..) => {
                self.resolve_constant(def_id).collect_err(&mut self.err);
            }
            _ => {}
        }

        hir::intravisit::walk_item(self, item);

        self.pop_rib(ValueNS);
        self.pop_rib(TypeNS);
    }

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem<'tcx>) {
        let def_id = self
            .genv
            .maybe_extern_id(impl_item.owner_id.def_id)
            .map(|def_id| OwnerId { def_id });

        self.push_rib(TypeNS, RibKind::Normal);
        self.define_generics(def_id);
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            self.resolve_fn_sig(def_id).collect_err(&mut self.err);
        }
        hir::intravisit::walk_impl_item(self, impl_item);
        self.pop_rib(TypeNS);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem<'tcx>) {
        let def_id = self
            .genv
            .maybe_extern_id(trait_item.owner_id.def_id)
            .map(|def_id| OwnerId { def_id });

        self.push_rib(TypeNS, RibKind::Normal);
        self.define_generics(def_id);
        if let hir::TraitItemKind::Fn(..) = trait_item.kind {
            self.resolve_fn_sig(def_id).collect_err(&mut self.err);
        }
        hir::intravisit::walk_trait_item(self, trait_item);
        self.pop_rib(TypeNS);
    }
}

#[derive(Debug)]
enum RibKind {
    /// Any other rib without extra rules.
    Normal,
    /// We pass through a module. Lookups of items should stop here.
    Module,
}

#[derive(Debug)]
struct Rib {
    kind: RibKind,
    bindings: FxHashMap<Symbol, hir::def::Res>,
}

impl Rib {
    fn new(kind: RibKind) -> Self {
        Self { kind, bindings: Default::default() }
    }
}

fn module_children(tcx: TyCtxt, def_id: DefId) -> &[ModChild] {
    #[expect(clippy::disallowed_methods, reason = "modules cannot have extern specs")]
    if let Some(local_id) = def_id.as_local() {
        tcx.module_children_local(local_id)
    } else {
        tcx.module_children(def_id)
    }
}

fn glob_imports<'tcx>(tcx: TyCtxt<'tcx>, path: &hir::UsePath) -> &'tcx [ModChild] {
    let res = path.segments.last().unwrap().res;
    let hir::def::Res::Def(DefKind::Mod, module_id) = res else {
        return &[];
    };
    module_children(tcx, module_id)
}

/// Return true if the item has a `#[prelude_import]` annotation
fn is_prelude_import(tcx: TyCtxt, item: &hir::Item) -> bool {
    tcx.hir()
        .attrs(item.hir_id())
        .iter()
        .any(|attr| attr.path_matches(&[sym::prelude_import]))
}

/// Abstraction over [`surface::PathSegment`] and [`surface::ExprPathSegment`]
trait Segment {
    fn record_segment_res(resolver: &mut CrateResolver, segment: &Self, res: fhir::Res);
    fn ident(&self) -> Ident;
}

impl Segment for surface::PathSegment {
    fn record_segment_res(resolver: &mut CrateResolver, segment: &Self, res: fhir::Res) {
        resolver
            .output
            .path_res_map
            .insert(segment.node_id, fhir::PartialRes::new(res));
    }

    fn ident(&self) -> Ident {
        self.ident
    }
}

impl Segment for surface::ExprPathSegment {
    fn record_segment_res(_resolver: &mut CrateResolver, _segment: &Self, _res: fhir::Res) {}

    fn ident(&self) -> Ident {
        self.ident
    }
}

impl Segment for Ident {
    fn record_segment_res(_resolver: &mut CrateResolver, _segment: &Self, _res: fhir::Res) {}

    fn ident(&self) -> Ident {
        *self
    }
}

struct ItemResolver<'a, 'genv, 'tcx> {
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    opaque: Option<LocalDefId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> ItemResolver<'a, 'genv, 'tcx> {
    fn run(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: MaybeExternId<OwnerId>,
        f: impl FnOnce(&mut ItemResolver),
    ) -> Result {
        let mut item_resolver = ItemResolver::new(resolver, owner_id)?;
        f(&mut item_resolver);
        item_resolver.errors.into_result()
    }

    fn new(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: MaybeExternId<OwnerId>,
    ) -> Result<Self> {
        let tcx = resolver.genv.tcx();
        let sess = resolver.genv.sess();
        let opaque = match tcx.hir_owner_node(owner_id.local_id()) {
            hir::OwnerNode::Item(item) => OpaqueTypeCollector::collect_item(sess, item)?,
            hir::OwnerNode::ImplItem(impl_item) => {
                OpaqueTypeCollector::collect_impl_item(sess, impl_item)?
            }
            hir::OwnerNode::TraitItem(trait_item) => {
                OpaqueTypeCollector::collect_trait_item(sess, trait_item)?
            }
            node @ (hir::OwnerNode::ForeignItem(_)
            | hir::OwnerNode::Crate(_)
            | hir::OwnerNode::Synthetic) => {
                bug!("unsupported node {node:?}")
            }
        };

        let errors = Errors::new(resolver.genv.sess());
        Ok(Self { resolver, opaque, errors })
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

    fn resolve_type_path(&mut self, path: &surface::Path) {
        if let Some(partial_res) = self.resolver.resolve_path_with_ribs(&path.segments, TypeNS) {
            self.resolver
                .output
                .path_res_map
                .insert(path.node_id, partial_res);
        } else {
            self.errors.emit(errors::UnresolvedPath::new(path));
        }
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
        self.resolve_type_path(path);
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
    }
}

struct OpaqueTypeCollector<'sess> {
    opaque: Option<LocalDefId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
    errors: Errors<'sess>,
}

impl<'sess> OpaqueTypeCollector<'sess> {
    fn new(sess: &'sess FluxSession) -> Self {
        Self { opaque: None, errors: Errors::new(sess) }
    }

    fn collect_item(sess: &'sess FluxSession, item: &hir::Item) -> Result<Option<LocalDefId>> {
        let mut collector = Self::new(sess);
        hir::intravisit::walk_item(&mut collector, item);
        collector.into_result()
    }

    fn collect_impl_item(
        sess: &'sess FluxSession,
        impl_item: &hir::ImplItem,
    ) -> Result<Option<LocalDefId>> {
        let mut collector = Self::new(sess);
        hir::intravisit::walk_impl_item(&mut collector, impl_item);
        collector.into_result()
    }

    fn collect_trait_item(
        sess: &'sess FluxSession,
        trait_item: &hir::TraitItem,
    ) -> Result<Option<LocalDefId>> {
        let mut collector = Self::new(sess);
        hir::intravisit::walk_trait_item(&mut collector, trait_item);
        collector.into_result()
    }

    fn into_result(self) -> Result<Option<LocalDefId>> {
        self.errors.into_result()?;
        Ok(self.opaque)
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for OpaqueTypeCollector<'_> {
    fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx>) {
        if let hir::TyKind::OpaqueDef(opaque_ty, ..) = ty.kind {
            if self.opaque.is_some() {
                self.errors.emit(errors::UnsupportedSignature::new(
                    ty.span,
                    "duplicate opaque types in signature",
                ));
            } else {
                self.opaque = Some(opaque_ty.def_id);
            }
        }
        hir::intravisit::walk_ty(self, ty);
    }
}

fn builtin_types_rib() -> Rib {
    Rib {
        kind: RibKind::Normal,
        bindings: PrimTy::ALL
            .into_iter()
            .map(|pty| (pty.name(), hir::def::Res::PrimTy(pty)))
            .collect(),
    }
}

fn mk_crate_mapping(tcx: TyCtxt) -> UnordMap<Symbol, DefId> {
    let mut map = UnordMap::default();
    map.insert(kw::Crate, CRATE_DEF_ID.to_def_id());
    for cnum in tcx.crates(()) {
        let name = tcx.crate_name(*cnum);
        if let Some(extern_crate) = tcx.extern_crate(*cnum)
            && extern_crate.is_direct()
        {
            map.insert(name, cnum.as_def_id());
        }
    }
    map
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
