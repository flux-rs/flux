pub(crate) mod refinement_resolver;

use std::collections::hash_map;

use flux_common::result::{ErrorCollector, ResultExt};
use flux_errors::Errors;
use flux_middle::{
    ResolverOutput, Specs,
    def_id::{FluxDefId, FluxLocalDefId, MaybeExternId},
    fhir,
    fhir::{
        Namespace::{self, *},
        PerNS,
    },
    global_env::GlobalEnv,
};
use flux_syntax::{
    surface::{self, Ident, visit::Visitor as _},
    symbols::sym,
};
use hir::{ItemId, ItemKind, OwnerId, def::DefKind};
use itertools::Itertools;
use rustc_data_structures::unord::{ExtendUnord, UnordMap};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    self as hir, CRATE_HIR_ID, CRATE_OWNER_ID, ParamName, PrimTy, def::CtorOf, def_id::CRATE_DEF_ID,
};
use rustc_middle::{metadata::ModChild, ty::TyCtxt};
use rustc_span::{Span, Symbol, def_id::DefId, symbol::kw};

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

    genv.tcx().hir_walk_toplevel_module(&mut resolver);

    resolver.into_output()
}

pub(crate) struct CrateResolver<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    specs: &'genv Specs,
    output: ResolverOutput,
    ribs: PerNS<Vec<Rib>>,
    /// A mapping from the names of all imported crates to their [`DefId`]
    crates: UnordMap<Symbol, DefId>,
    /// Names available everywhere: Rust builtin types plus flux's global funcs (theory funcs, `cast`)
    /// and primitive sorts.
    prelude: PerNS<Rib>,
    qualifiers: UnordMap<Symbol, FluxLocalDefId>,
    primop_props: UnordMap<Symbol, FluxDefId>,
    err: Option<ErrorGuaranteed>,
    /// The most recent module we have visited. Used to check for visibility of other items from
    /// this module.
    current_module: OwnerId,
}

/// Map to keep track of names defined in a scope
#[derive(Default)]
struct DefinitionMap {
    defined: UnordMap<Ident, ()>,
}

impl DefinitionMap {
    fn define(&mut self, name: Ident) -> std::result::Result<(), errors::DuplicateDefinition> {
        match self.defined.entry(name) {
            hash_map::Entry::Occupied(entry) => {
                Err(errors::DuplicateDefinition {
                    span: name.span,
                    previous_definition: entry.key().span,
                    name,
                })
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(());
                Ok(())
            }
        }
    }
}

impl<'genv, 'tcx> CrateResolver<'genv, 'tcx> {
    pub fn new(genv: GlobalEnv<'genv, 'tcx>, specs: &'genv Specs) -> Self {
        Self {
            genv,
            output: ResolverOutput::default(),
            specs,
            ribs: PerNS { type_ns: vec![], value_ns: vec![], macro_ns: vec![], flux_fn_ns: vec![] },
            crates: mk_crate_mapping(genv.tcx()),
            prelude: PerNS {
                type_ns: builtin_types_rib(),
                value_ns: Rib::new(RibKind::Misc),
                macro_ns: Rib::new(RibKind::Misc),
                flux_fn_ns: theory_funcs_rib(),
            },
            err: None,
            qualifiers: Default::default(),
            primop_props: Default::default(),
            current_module: CRATE_OWNER_ID,
        }
    }

    #[allow(clippy::disallowed_methods, reason = "`flux_items_by_parent` is the source of truth")]
    fn define_flux_global_items(&mut self) {
        // Note that names are defined globally so we check for duplicates globally in the crate.
        let mut definitions = DefinitionMap::default();
        for (parent, items) in &self.specs.flux_items_by_parent {
            for item in items {
                // NOTE: This is putting all items in the same namespace. In principle, we could have
                // qualifiers in a different namespace.
                definitions
                    .define(item.name())
                    .emit(&self.genv)
                    .collect_err(&mut self.err);

                match item {
                    surface::FluxItem::Qualifier(qual) => {
                        let def_id = FluxLocalDefId::new(parent.def_id, qual.name.name);
                        self.qualifiers.insert(qual.name.name, def_id);
                    }
                    surface::FluxItem::FuncDef(defn) => {
                        let parent = parent.def_id.to_def_id();
                        let name = defn.name.name;
                        let def_id = FluxDefId::new(parent, name);
                        let kind = fhir::SpecFuncKind::Def(def_id);
                        self.define_in_prelude(name, fhir::Res::GlobalFunc(kind), ReftNS);
                    }
                    surface::FluxItem::PrimOpProp(primop_prop) => {
                        let name = primop_prop.name.name;
                        let parent = parent.def_id.to_def_id();
                        let def_id = FluxDefId::new(parent, name);
                        self.primop_props.insert(name, def_id);
                    }
                    surface::FluxItem::SortDecl(sort_decl) => {
                        let def_id = FluxDefId::new(parent.def_id.to_def_id(), sort_decl.name.name);
                        self.define_in_prelude(
                            sort_decl.name.name,
                            fhir::Res::UserSort(def_id),
                            TypeNS,
                        );
                    }
                }
            }
        }
    }

    fn define_items(&mut self, item_ids: impl IntoIterator<Item = &'tcx ItemId>) {
        for item_id in item_ids {
            let item = self.genv.tcx().hir_item(*item_id);
            let def_kind = match item.kind {
                ItemKind::Use(path, kind) => {
                    match kind {
                        hir::UseKind::Single(ident) => {
                            let name = ident.name;
                            if let Some(res) = path.res.value_ns
                                && let Ok(res) = fhir::Res::try_from(res)
                            {
                                self.define_res_in(name, res, ValueNS);
                            }
                            if let Some(res) = path.res.type_ns
                                && let Ok(res) = fhir::Res::try_from(res)
                            {
                                self.define_res_in(name, res, TypeNS);
                            }
                        }
                        hir::UseKind::Glob => {
                            let is_prelude = is_prelude_import(self.genv.tcx(), item);
                            for mod_child in self.glob_imports(path) {
                                if let Ok(res) = fhir::Res::try_from(mod_child.res)
                                    && let Some(ns @ (TypeNS | ValueNS)) = res.ns()
                                {
                                    let name = mod_child.ident.name;
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
                ItemKind::Union(..) => DefKind::Union,
                ItemKind::Trait(..) => DefKind::Trait,
                ItemKind::Mod(..) => DefKind::Mod,
                ItemKind::Const(..) => DefKind::Const,
                ItemKind::ForeignMod { items, .. } => {
                    self.define_foreign_items(items);
                    continue;
                }
                _ => continue,
            };
            if let Some(ns) = def_kind.ns().map(Namespace::from)
                && let Some(ident) = item.kind.ident()
            {
                self.define_res_in(
                    ident.name,
                    fhir::Res::Def(def_kind, item.owner_id.to_def_id()),
                    ns,
                );
            }
        }
    }

    fn define_foreign_items(&mut self, items: &[rustc_hir::ForeignItemId]) {
        for item_id in items {
            let item = self.genv.tcx().hir_foreign_item(*item_id);
            match item.kind {
                rustc_hir::ForeignItemKind::Type => {
                    self.define_res_in(
                        item.ident.name,
                        fhir::Res::Def(DefKind::ForeignTy, item.owner_id.to_def_id()),
                        TypeNS,
                    );
                }
                rustc_hir::ForeignItemKind::Fn(..) | rustc_hir::ForeignItemKind::Static(..) => {}
            }
        }
    }

    /// Define `name` in the innermost rib of `ns`. If the rib already binds `name`, keep the existing
    /// binding and return it.
    fn define_res_in(
        &mut self,
        name: Symbol,
        res: fhir::Res<surface::NodeId>,
        ns: Namespace,
    ) -> Option<fhir::Res<surface::NodeId>> {
        match self.ribs[ns].last_mut().unwrap().bindings.entry(name) {
            hash_map::Entry::Occupied(entry) => Some(*entry.get()),
            hash_map::Entry::Vacant(entry) => {
                entry.insert(res);
                None
            }
        }
    }

    fn define_in_prelude(&mut self, name: Symbol, res: fhir::Res<surface::NodeId>, ns: Namespace) {
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
            .tcx()
            .hir_get_generics(def_id.local_id().def_id)
            .unwrap();
        for param in generics.params {
            let def_kind = self.genv.tcx().def_kind(param.def_id);
            if let ParamName::Plain(name) = param.name
                && let Some(ns) = def_kind.ns().map(Namespace::from)
            {
                debug_assert!(matches!(def_kind, DefKind::TyParam | DefKind::ConstParam));
                let param_id = self.genv.maybe_extern_id(param.def_id).resolved_id();
                self.define_res_in(name.name, fhir::Res::Def(def_kind, param_id), ns);
            }
        }
    }

    fn resolve_flux_items(&mut self, parent: OwnerId) {
        let Some(items) = self.specs.flux_items_by_parent.get(&parent) else { return };
        for item in items {
            RefinementResolver::resolve_flux_item(self, item).collect_err(&mut self.err);
        }
    }

    fn resolve_item(&mut self, item: &surface::Item, item_id: MaybeExternId<OwnerId>) -> Result {
        ItemResolver::run(self, item_id, |item_resolver| item_resolver.visit_item(item))?;
        RefinementResolver::resolve_item(self, item)
    }

    fn resolve_trait_item(
        &mut self,
        item: &surface::TraitItemFn,
        item_id: MaybeExternId<OwnerId>,
    ) -> Result {
        ItemResolver::run(self, item_id, |item_resolver| item_resolver.visit_trait_item(item))?;
        RefinementResolver::resolve_trait_item(self, item)
    }

    fn resolve_impl_item(
        &mut self,
        item: &surface::ImplItemFn,
        item_id: MaybeExternId<OwnerId>,
    ) -> Result {
        ItemResolver::run(self, item_id, |item_resolver| item_resolver.visit_impl_item(item))?;
        RefinementResolver::resolve_impl_item(self, item)
    }

    fn resolve_path_with_ribs<S: Segment>(
        &mut self,
        segments: &[S],
        ns: Namespace,
    ) -> Option<fhir::PartialRes<surface::NodeId>> {
        let mut module: Option<Module> = None;
        for (segment_idx, segment) in segments.iter().enumerate() {
            let is_last = segment_idx + 1 == segments.len();
            let ns = if is_last { ns } else { TypeNS };

            let base_res = if let Some(module) = &module {
                self.resolve_ident_in_module(module, segment.ident(), ns)?
            } else {
                self.resolve_ident_with_ribs(segment.ident(), ns)?
            };

            S::record_segment_res(self, segment, base_res);

            if is_last {
                return Some(fhir::PartialRes::new(base_res));
            }

            match base_res {
                fhir::Res::Def(DefKind::Mod, module_id) => {
                    module = Some(Module::new(ModuleKind::Mod, module_id));
                }
                fhir::Res::Def(DefKind::Trait, module_id) => {
                    module = Some(Module::new(ModuleKind::Trait, module_id));
                }
                fhir::Res::Def(DefKind::Enum, module_id) => {
                    module = Some(Module::new(ModuleKind::Enum, module_id));
                }
                _ => {
                    return Some(fhir::PartialRes::with_unresolved_segments(
                        base_res,
                        segments.len() - segment_idx - 1,
                    ));
                }
            }
        }
        None
    }

    fn resolve_ident_with_ribs(
        &self,
        ident: Ident,
        ns: Namespace,
    ) -> Option<fhir::Res<surface::NodeId>> {
        let mut ribs = self.ribs[ns].iter().rev();
        while let Some(rib) = ribs.next() {
            if let Some(res) = rib.bindings.get(&ident.name) {
                return Some(*res);
            }
            match rib.kind {
                // A module boundary stops item resolution.
                RibKind::Module => break,
                // A variant is a barrier that hides refinement params bound in the `refined_by` *enclosing*
                // scope, but not other refinement bindings in other scopes (e.g. flux funcs in the parent module).
                // FIXME: this is skipping potential names defined inside a `const _ = { ... }` or other similar
                // "transparent modules".
                RibKind::Variant => {
                    ribs.take_while_ref(|rib| !matches!(rib.kind, RibKind::Module))
                        .for_each(drop);
                }
                _ => {}
            }
        }
        if ns == TypeNS {
            if let Some(crate_id) = self.crates.get(&ident.name) {
                return Some(fhir::Res::Def(DefKind::Mod, *crate_id));
            }
            // FIXME: `crate` and `super` should only be allowed as the first segment
            if ident.name == kw::Crate {
                return Some(fhir::Res::Def(DefKind::Mod, CRATE_DEF_ID.to_def_id()));
            }
            if ident.name == kw::Super
                && let Some(parent) = self.genv.tcx().opt_local_parent(self.current_module.def_id)
            {
                return Some(fhir::Res::Def(DefKind::Mod, parent.to_def_id()));
            }
        }

        if let Some(res) = self.prelude[ns].bindings.get(&ident.name) {
            return Some(*res);
        }
        None
    }

    fn glob_imports(
        &mut self,
        path: &hir::UsePath,
    ) -> impl Iterator<Item = &'tcx ModChild> + use<'tcx> {
        // The path for the prelude import is not resolved anymore after <https://github.com/rust-lang/rust/pull/145322>,
        // so we resolve all paths here. If this ever causes problems, we could use the resolution in the `UsePath` for
        // non-prelude glob imports.
        let tcx = self.genv.tcx();
        let curr_mod = self.current_module.to_def_id();
        self.resolve_path_with_ribs(path.segments, TypeNS)
            .and_then(|partial_res| partial_res.full_res())
            .and_then(|res| {
                if let fhir::Res::Def(DefKind::Mod, module_id) = res {
                    Some(module_id)
                } else {
                    None
                }
            })
            .into_iter()
            .flat_map(move |module_id| visible_module_children(tcx, module_id, curr_mod))
    }

    fn resolve_ident_in_module(
        &self,
        module: &Module,
        ident: Ident,
        ns: Namespace,
    ) -> Option<fhir::Res<surface::NodeId>> {
        let tcx = self.genv.tcx();
        match module.kind {
            ModuleKind::Mod => {
                // Module children are Rust items, so we only ever resolve them in a Rust namespace.
                let rustc_ns = ns.to_rustc()?;
                let module_id = module.def_id;
                let current_mod = self.current_module.to_def_id();
                visible_module_children(tcx, module_id, current_mod)
                    .find(|child| {
                        child.res.matches_ns(rustc_ns)
                            && tcx.hygienic_eq(ident, child.ident, current_mod)
                    })
                    .and_then(|child| fhir::Res::<surface::NodeId>::try_from(child.res).ok())
            }
            ModuleKind::Trait => {
                // Associated items are Rust items, so we only ever resolve them in a Rust namespace.
                let rustc_ns = ns.to_rustc()?;
                let trait_id = module.def_id;
                tcx.associated_items(trait_id)
                    .find_by_ident_and_namespace(tcx, ident, rustc_ns, trait_id)
                    .map(|assoc| fhir::Res::Def(assoc.kind.as_def_kind(), assoc.def_id))
            }
            ModuleKind::Enum => {
                tcx.adt_def(module.def_id)
                    .variants()
                    .iter()
                    .find(|data| data.name == ident.name)
                    .and_then(|data| {
                        let (kind, def_id) = match (ns, data.ctor) {
                            (TypeNS, _) => (DefKind::Variant, data.def_id),
                            (ValueNS, Some((ctor_kind, ctor_id))) => {
                                (DefKind::Ctor(CtorOf::Variant, ctor_kind), ctor_id)
                            }
                            _ => return None,
                        };
                        Some(fhir::Res::Def(kind, def_id))
                    })
            }
        }
    }

    pub fn into_output(self) -> Result<ResolverOutput> {
        self.err.into_result()?;
        Ok(self.output)
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for CrateResolver<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.genv.tcx()
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

        hir::intravisit::walk_mod(self, module);

        self.pop_rib(ValueNS);
        self.pop_rib(TypeNS);
        self.current_module = old_mod;
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        self.push_rib(TypeNS, RibKind::Misc);
        self.push_rib(ValueNS, RibKind::Misc);

        let item_ids = block.stmts.iter().filter_map(|stmt| {
            if let hir::StmtKind::Item(item_id) = &stmt.kind { Some(item_id) } else { None }
        });
        self.define_items(item_ids);
        self.resolve_flux_items(self.genv.tcx().hir_get_parent_item(block.hir_id));

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

        self.push_rib(TypeNS, RibKind::Misc);
        self.push_rib(ValueNS, RibKind::Misc);

        match item.kind {
            ItemKind::Trait(..) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    fhir::Res::SelfTyParam { trait_: def_id.resolved_id() },
                    TypeNS,
                );
            }
            ItemKind::Impl(hir::Impl { of_trait, .. }) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    fhir::Res::SelfTyAlias {
                        alias_to: def_id.resolved_id(),
                        is_trait_impl: of_trait.is_some(),
                    },
                    TypeNS,
                );
            }
            ItemKind::TyAlias(..) => {
                self.define_generics(def_id);
            }
            ItemKind::Enum(..) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    fhir::Res::SelfTyAlias { alias_to: def_id.resolved_id(), is_trait_impl: false },
                    TypeNS,
                );
            }
            ItemKind::Struct(..) => {
                self.define_generics(def_id);
                self.define_res_in(
                    kw::SelfUpper,
                    fhir::Res::SelfTyAlias { alias_to: def_id.resolved_id(), is_trait_impl: false },
                    TypeNS,
                );
            }
            ItemKind::Fn { .. } => {
                self.define_generics(def_id);
            }
            _ => {}
        }
        if let Some(item) = self.specs.get_item(def_id.local_id()) {
            self.resolve_item(item, def_id).collect_err(&mut self.err);
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

        self.push_rib(TypeNS, RibKind::Misc);
        if let Some(item) = self.specs.get_impl_item(def_id.local_id()) {
            self.define_generics(def_id);
            self.resolve_impl_item(item, def_id)
                .collect_err(&mut self.err);
        }
        hir::intravisit::walk_impl_item(self, impl_item);
        self.pop_rib(TypeNS);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem<'tcx>) {
        let def_id = self
            .genv
            .maybe_extern_id(trait_item.owner_id.def_id)
            .map(|def_id| OwnerId { def_id });

        self.push_rib(TypeNS, RibKind::Misc);
        if let Some(item) = self.specs.get_trait_item(def_id.local_id()) {
            self.define_generics(def_id);
            self.resolve_trait_item(item, def_id)
                .collect_err(&mut self.err);
        }
        hir::intravisit::walk_trait_item(self, trait_item);
        self.pop_rib(TypeNS);
    }
}

/// Akin to `rustc_resolve::Module` but specialized to what we support
#[derive(Debug)]
struct Module {
    kind: ModuleKind,
    def_id: DefId,
}

impl Module {
    fn new(kind: ModuleKind, def_id: DefId) -> Self {
        Self { kind, def_id }
    }
}

/// Akin to `rustc_resolve::ModuleKind` but specialized to what we support
#[derive(Debug)]
enum ModuleKind {
    Mod,
    Trait,
    Enum,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum RibKind {
    /// An rib with no special rules.
    Misc,
    /// A module boundary. This is a barrier for item resolution.
    Module,
    /// A function signature's inputs (arguments and `requires`). `@` binders are legal here.
    FnInput,
    /// A function signature's output (return type and `ensures`). `#` binders are legal here.
    FnOutput,
    /// An enum variant. `@` binders are legal here. This is a barrier scope because variants
    /// are nested within `refined_by` params.
    Variant,
    /// The input position of an `Fn`-trait bound (e.g. the `T` in `FnMut(T) -> S`). `@` binders are
    /// legal here.
    FnTraitInput,
}

#[derive(Debug)]
struct Rib {
    kind: RibKind,
    bindings: UnordMap<Symbol, fhir::Res<surface::NodeId>>,
}

impl Rib {
    fn new(kind: RibKind) -> Self {
        Self { kind, bindings: Default::default() }
    }
}

fn module_children(tcx: TyCtxt<'_>, def_id: DefId) -> &[ModChild] {
    #[expect(clippy::disallowed_methods, reason = "modules cannot have extern specs")]
    if let Some(local_id) = def_id.as_local() {
        tcx.module_children_local(local_id)
    } else {
        tcx.module_children(def_id)
    }
}

/// Iterator over module children visible form `curr_mod`
fn visible_module_children(
    tcx: TyCtxt<'_>,
    module_id: DefId,
    curr_mod: DefId,
) -> impl Iterator<Item = &ModChild> {
    module_children(tcx, module_id)
        .iter()
        .filter(move |child| child.vis.is_accessible_from(curr_mod, tcx))
}

/// Return true if the item has a `#[prelude_import]` annotation
fn is_prelude_import(tcx: TyCtxt, item: &hir::Item) -> bool {
    tcx.hir_attrs(item.hir_id())
        .iter()
        .any(|attr| attr.path_matches(&[sym::prelude_import]))
}

/// Abstraction over a "segment" so we can use [`CrateResolver::resolve_path_with_ribs`] with paths
/// from different sources  (e.g., [`surface::PathSegment`], [`surface::ExprPathSegment`])
trait Segment: std::fmt::Debug {
    fn record_segment_res(
        resolver: &mut CrateResolver,
        segment: &Self,
        res: fhir::Res<surface::NodeId>,
    );
    fn ident(&self) -> Ident;
}

impl Segment for surface::PathSegment {
    fn record_segment_res(
        resolver: &mut CrateResolver,
        segment: &Self,
        res: fhir::Res<surface::NodeId>,
    ) {
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
    fn record_segment_res(
        resolver: &mut CrateResolver,
        segment: &Self,
        res: fhir::Res<surface::NodeId>,
    ) {
        resolver
            .output
            .path_res_map
            .insert(segment.node_id, fhir::PartialRes::new(res));
    }

    fn ident(&self) -> Ident {
        self.ident
    }
}

impl Segment for Ident {
    fn record_segment_res(
        _resolver: &mut CrateResolver,
        _segment: &Self,
        _res: fhir::Res<surface::NodeId>,
    ) {
    }

    fn ident(&self) -> Ident {
        *self
    }
}

impl Segment for hir::PathSegment<'_> {
    fn record_segment_res(
        _resolver: &mut CrateResolver,
        _segment: &Self,
        _res: fhir::Res<surface::NodeId>,
    ) {
    }

    fn ident(&self) -> Ident {
        self.ident
    }
}

struct ItemResolver<'a, 'genv, 'tcx> {
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    errors: Errors<'genv>,
    item_id: MaybeExternId<OwnerId>,
}

impl<'a, 'genv, 'tcx> ItemResolver<'a, 'genv, 'tcx> {
    fn run(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item_id: MaybeExternId<OwnerId>,
        f: impl FnOnce(&mut ItemResolver),
    ) -> Result {
        let mut item_resolver = ItemResolver::new(resolver, item_id);
        f(&mut item_resolver);
        item_resolver.errors.into_result()
    }

    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>, item_id: MaybeExternId<OwnerId>) -> Self {
        let errors = Errors::new(resolver.genv.sess());
        Self { resolver, errors, item_id }
    }

    fn resolve_type_path(&mut self, path: &surface::Path) {
        self.resolve_path_in(path, TypeNS);
    }

    fn resolve_path_in(&mut self, path: &surface::Path, ns: Namespace) {
        if let Some(partial_res) = self.resolver.resolve_path_with_ribs(&path.segments, ns) {
            self.resolver
                .output
                .path_res_map
                .insert(path.node_id, partial_res);
        } else {
            self.emit_unresolved_path(path, ns);
        }
    }

    fn resolve_attrs(&mut self, node_id: surface::NodeId, attrs: &[surface::Attr]) {
        for attr in attrs {
            match attr {
                surface::Attr::Qualifiers(names) => self.resolve_qualifiers(node_id, names),
                surface::Attr::Reveal(names) => self.resolve_reveals(node_id, names),
                surface::Attr::AssumeParametric(names) => {
                    self.resolve_parametric_params(node_id, names);
                }
                _ => {}
            }
        }
    }

    fn resolve_parametric_params(&mut self, node_id: surface::NodeId, names: &[Ident]) {
        let tcx = self.resolver.genv.tcx();
        let generics = tcx.generics_of(self.item_id.resolved_id());
        let param_map: UnordMap<Symbol, DefId> = (0..generics.count())
            .map(|i| generics.param_at(i, tcx))
            .map(|p| (p.name, p.def_id))
            .collect();
        let mut params = Vec::with_capacity(names.len());
        for name in names {
            if let Some(&def_id) = param_map.get(&name.name) {
                params.push(def_id);
            } else {
                self.errors
                    .emit(errors::UnknownParametricParam::new(name.span));
            }
        }
        self.resolver
            .output
            .parametric_param_res_map
            .insert(node_id, params);
    }

    fn resolve_qualifiers(&mut self, node_id: surface::NodeId, qual_names: &[Ident]) {
        let mut qualifiers = Vec::with_capacity(qual_names.len());
        for qual in qual_names {
            if let Some(def_id) = self.resolver.qualifiers.get(&qual.name) {
                qualifiers.push(*def_id);
            } else {
                self.errors.emit(errors::UnknownQualifier::new(qual.span));
            }
        }
        self.resolver
            .output
            .qualifier_res_map
            .insert(node_id, qualifiers);
    }

    fn resolve_reveals(&mut self, item_id: surface::NodeId, reveal_names: &[Ident]) {
        let mut reveals = Vec::with_capacity(reveal_names.len());
        for reveal in reveal_names {
            if let Some(fhir::Res::GlobalFunc(kind)) =
                self.resolver.resolve_ident_with_ribs(*reveal, ReftNS)
                && let Some(def_id) = kind.def_id()
            {
                reveals.push(def_id);
            } else {
                self.errors
                    .emit(errors::UnknownRevealDefinition::new(reveal.span));
            }
        }
        self.resolver.output.reveal_res_map.insert(item_id, reveals);
    }

    fn emit_unresolved_path(&mut self, path: &surface::Path, ns: Namespace) {
        self.errors.emit(errors::UnresolvedName {
            span: path.span,
            name: path.segments.iter().map(|segment| segment.ident).join("::"),
            kind: ns.descr(),
        });
    }
}

impl surface::visit::Visitor for ItemResolver<'_, '_, '_> {
    fn visit_item(&mut self, item: &surface::Item) {
        self.resolve_attrs(item.node_id, &item.attrs);
        surface::visit::walk_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &surface::TraitItemFn) {
        self.resolve_attrs(item.node_id, &item.attrs);
        surface::visit::walk_trait_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &surface::ImplItemFn) {
        self.resolve_attrs(item.node_id, &item.attrs);
        surface::visit::walk_impl_item(self, item);
    }

    fn visit_trait(&mut self, trait_: &surface::Trait) {
        let mut definitions = DefinitionMap::default();
        for assoc_reft in &trait_.assoc_refinements {
            let _ = definitions.define(assoc_reft.name).emit(&self.errors);
        }
        surface::visit::walk_trait(self, trait_);
    }

    fn visit_impl(&mut self, impl_: &surface::Impl) {
        let mut definitions = DefinitionMap::default();
        for assoc_reft in &impl_.assoc_refinements {
            let _ = definitions.define(assoc_reft.name).emit(&self.errors);
        }
        surface::visit::walk_impl(self, impl_);
    }

    fn visit_generic_arg(&mut self, arg: &surface::GenericArg) {
        if let surface::GenericArgKind::Type(ty) = &arg.kind
            && let Some(path) = ty.is_potential_const_arg()
        {
            // We parse const arguments as path types as we cannot distinguish them during
            // parsing. We try to resolve that ambiguity by attempting resolution in both the
            // type and value namespaces. If we resolved the path in the value namespace, we
            // transform it into a generic const argument.
            let check_ns = |ns| {
                self.resolver
                    .resolve_ident_with_ribs(path.last().ident, ns)
                    .is_some()
            };

            if !check_ns(TypeNS) && check_ns(ValueNS) {
                self.resolve_path_in(path, ValueNS);
                return;
            }
        }
        surface::visit::walk_generic_arg(self, arg);
    }

    fn visit_const_arg(&mut self, const_arg: &surface::ConstArg) {
        if let surface::ConstArgKind::Path(path) = &const_arg.kind {
            self.resolve_path_in(path, ValueNS);
            surface::visit::walk_path(self, path);
        }
    }

    fn visit_path(&mut self, path: &surface::Path) {
        self.resolve_type_path(path);
        surface::visit::walk_path(self, path);
    }
}

/// The [`Namespace::TypeNS`] prelude: builtin Rust types (`bool`, `i32`, `str`, ...) together with
/// the sort-only primitive sorts (`int`, `real`, `Set`, `Map`, `ptr`). Sorts and types share the
/// type namespace; `bool`/`char`/`str` are resolved as [`fhir::Res::PrimTy`] and their sort is
/// derived in `conv_sort_path` (see [`fhir::PrimSort`]).
fn builtin_types_rib() -> Rib {
    use flux_middle::fhir::PrimSort;
    let sorts = PrimSort::ALL
        .into_iter()
        .map(|prim| (prim.name(), fhir::Res::PrimSort(prim)));
    let types = PrimTy::ALL
        .into_iter()
        .map(|pty| (pty.name(), fhir::Res::PrimTy(pty)));

    // Types go after such that they override sorts with the same name
    let bindings = sorts.chain(types).collect();
    Rib { kind: RibKind::Misc, bindings }
}

/// The [`Namespace::ReftNS`] prelude: theory functions and `cast`.
fn theory_funcs_rib() -> Rib {
    let mut rib = Rib::new(RibKind::Misc);
    rib.bindings.extend_unord(
        flux_middle::THEORY_FUNCS
            .items()
            .map(|(_, itf)| (itf.name, fhir::Res::GlobalFunc(fhir::SpecFuncKind::Thy(itf.itf)))),
    );
    rib.bindings
        .insert(sym::cast, fhir::Res::GlobalFunc(fhir::SpecFuncKind::Cast));
    rib
}

fn mk_crate_mapping(tcx: TyCtxt) -> UnordMap<Symbol, DefId> {
    let mut map = UnordMap::default();
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
    use rustc_span::{Ident, Span};

    /// A name that could not be resolved. `kind` is the user-facing description of what was being
    /// looked for (`"type"`, `"value"`, `"sort"`, ...); it is passed explicitly by each call site
    /// because it no longer matches the resolution [`Namespace`](flux_middle::fhir::Namespace)
    /// (e.g. sorts are resolved in the type namespace).
    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_name, code = E0999)]
    pub(crate) struct UnresolvedName {
        #[primary_span]
        #[label]
        pub span: Span,
        pub kind: &'static str,
        pub name: String,
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unknown_qualifier, code = E0999)]
    pub(super) struct UnknownQualifier {
        #[primary_span]
        span: Span,
    }

    impl UnknownQualifier {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unknown_reveal_definition, code = E0999)]
    pub(super) struct UnknownRevealDefinition {
        #[primary_span]
        span: Span,
    }

    impl UnknownRevealDefinition {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unknown_parametric_param, code = E0999)]
    pub(super) struct UnknownParametricParam {
        #[primary_span]
        span: Span,
    }

    impl UnknownParametricParam {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_duplicate_definition, code = E0999)]
    pub(super) struct DuplicateDefinition {
        #[primary_span]
        #[label]
        pub span: Span,
        #[label(desugar_previous_definition)]
        pub previous_definition: Span,
        pub name: Ident,
    }
}
