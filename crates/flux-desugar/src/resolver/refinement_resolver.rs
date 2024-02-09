use std::ops::ControlFlow;

use flux_common::index::IndexGen;
use flux_errors::ErrorCollector;
use flux_middle::{fhir, PathRes, ResolverOutput};
use flux_syntax::surface::{self, visit::Visitor as _, Ident, NodeId};
use rustc_data_structures::{
    fx::{FxIndexMap, IndexEntry},
    unord::UnordMap,
};
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def::DefKind, OwnerId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{sym, symbol::kw, ErrorGuaranteed, Symbol};

use super::CrateResolver;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ScopeKind {
    FnInput,
    FnOutput,
    Variant,
    Misc,
}

impl ScopeKind {
    fn is_barrier(self) -> bool {
        matches!(self, ScopeKind::FnInput | ScopeKind::Variant)
    }
}

/// Parameters used during gathering.
#[derive(Debug, Clone, Copy)]
struct ParamRes(fhir::ParamKind, NodeId);

impl ParamRes {
    fn kind(self) -> fhir::ParamKind {
        self.0
    }

    fn param_id(self) -> NodeId {
        self.1
    }
}

pub(crate) trait ScopedVisitor: Sized {
    fn is_box(&self, path: &surface::Path) -> bool;
    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()>;
    fn exit_scope(&mut self) {}

    fn wrap(self) -> ScopedVisitorWrapper<Self> {
        ScopedVisitorWrapper(self)
    }

    fn on_implicit_param(&mut self, _ident: Ident, _kind: fhir::ParamKind, _node_id: NodeId) {}
    fn on_generic_param(&mut self, _param: &surface::GenericParam) {}
    fn on_refine_param(&mut self, _name: Ident, _node_id: NodeId) {}
    fn on_enum_variant(&mut self, _variant: &surface::VariantDef) {}
    fn on_fn_sig(&mut self, _fn_sig: &surface::FnSig) {}
    fn on_fn_output(&mut self, _output: &surface::FnOutput) {}
    fn on_loc(&mut self, _loc: Ident, _node_id: NodeId) {}
    fn on_func(&mut self, _func: Ident, _node_id: NodeId) {}
    fn on_path(&mut self, _path: &surface::PathExpr) {}
    fn on_base_sort(&mut self, _sort: &surface::BaseSort) {}
}

pub(crate) struct ScopedVisitorWrapper<V>(V);

impl<V: ScopedVisitor> ScopedVisitorWrapper<V> {
    fn with_scope(&mut self, kind: ScopeKind, f: impl FnOnce(&mut Self)) {
        if let ControlFlow::Continue(_) = self.0.enter_scope(kind) {
            f(self);
            self.0.exit_scope();
        }
    }
}

impl<V> std::ops::Deref for ScopedVisitorWrapper<V> {
    type Target = V;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<V> std::ops::DerefMut for ScopedVisitorWrapper<V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<V: ScopedVisitor> surface::visit::Visitor for ScopedVisitorWrapper<V> {
    fn visit_trait_assoc_reft(&mut self, assoc_reft: &surface::TraitAssocReft) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_trait_assoc_reft(this, assoc_reft);
        });
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &surface::ImplAssocReft) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_impl_assoc_reft(this, assoc_reft);
        });
    }

    fn visit_qualifier(&mut self, qualifier: &surface::Qualifier) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_qualifier(this, qualifier);
        });
    }

    fn visit_defn(&mut self, defn: &surface::SpecFunc) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_defn(this, defn);
        });
    }

    fn visit_generic_param(&mut self, param: &surface::GenericParam) {
        self.on_generic_param(param);
        surface::visit::walk_generic_param(self, param);
    }

    fn visit_refine_param(&mut self, param: &surface::RefineParam) {
        self.on_refine_param(param.name, param.node_id);
        surface::visit::walk_refine_param(self, param);
    }

    fn visit_ty_alias(&mut self, ty_alias: &surface::TyAlias) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_ty_alias(this, ty_alias);
        });
    }

    fn visit_struct_def(&mut self, struct_def: &surface::StructDef) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_struct_def(this, struct_def);
        });
    }

    fn visit_enum_def(&mut self, enum_def: &surface::EnumDef) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_enum_def(this, enum_def);
        });
    }

    fn visit_variant(&mut self, variant: &surface::VariantDef) {
        self.with_scope(ScopeKind::Variant, |this| {
            this.on_enum_variant(variant);
            surface::visit::walk_variant(this, variant);
        });
    }

    fn visit_variant_ret(&mut self, ret: &surface::VariantRet) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_variant_ret(this, ret);
        });
    }

    fn visit_fn_sig(&mut self, fn_sig: &surface::FnSig) {
        self.with_scope(ScopeKind::FnInput, |this| {
            this.on_fn_sig(fn_sig);
            surface::visit::walk_fn_sig(this, fn_sig);
        });
    }

    fn visit_fn_output(&mut self, output: &surface::FnOutput) {
        self.with_scope(ScopeKind::FnOutput, |this| {
            this.on_fn_output(output);
            surface::visit::walk_fn_output(this, output);
        });
    }

    fn visit_fun_arg(&mut self, arg: &surface::Arg, idx: usize) {
        match arg {
            surface::Arg::Constr(bind, _, _, node_id) => {
                self.on_implicit_param(*bind, fhir::ParamKind::Colon, *node_id);
            }
            surface::Arg::StrgRef(loc, _, node_id) => {
                self.on_implicit_param(*loc, fhir::ParamKind::Loc(idx), *node_id);
            }
            surface::Arg::Ty(bind, ty, node_id) => {
                if let &Some(bind) = bind {
                    let param_kind = if let surface::TyKind::Base(bty) = &ty.kind {
                        if bty.is_hole() {
                            fhir::ParamKind::Error
                        } else {
                            fhir::ParamKind::Colon
                        }
                    } else {
                        fhir::ParamKind::Error
                    };
                    self.on_implicit_param(bind, param_kind, *node_id);
                }
            }
        }
        surface::visit::walk_fun_arg(self, arg);
    }

    fn visit_constraint(&mut self, constraint: &surface::Constraint) {
        if let surface::Constraint::Type(loc, _, node_id) = constraint {
            self.on_loc(*loc, *node_id);
        }
        surface::visit::walk_constraint(self, constraint);
    }

    fn visit_refine_arg(&mut self, arg: &surface::RefineArg) {
        match arg {
            surface::RefineArg::Bind(ident, kind, _, node_id) => {
                let kind = match kind {
                    surface::BindKind::At => fhir::ParamKind::At,
                    surface::BindKind::Pound => fhir::ParamKind::Pound,
                };
                self.on_implicit_param(*ident, kind, *node_id);
            }
            surface::RefineArg::Abs(..) => {
                self.with_scope(ScopeKind::Misc, |this| {
                    surface::visit::walk_refine_arg(this, arg);
                });
            }
            surface::RefineArg::Expr(expr) => self.visit_expr(expr),
        }
    }

    fn visit_path(&mut self, path: &surface::Path) {
        // skip holes because they don't have a corresponding `Res`
        if path.is_hole() {
            return;
        }

        for arg in &path.refine {
            self.with_scope(ScopeKind::Misc, |this| this.visit_refine_arg(arg));
        }

        let is_box = self.is_box(path);
        for (i, arg) in path.generics.iter().enumerate() {
            if is_box && i == 0 {
                self.visit_generic_arg(arg);
            } else {
                self.with_scope(ScopeKind::Misc, |this| this.visit_generic_arg(arg));
            }
        }
    }

    fn visit_ty(&mut self, ty: &surface::Ty) {
        let node_id = ty.node_id;
        match &ty.kind {
            surface::TyKind::Exists { bind, .. } => {
                self.with_scope(ScopeKind::Misc, |this| {
                    this.on_refine_param(*bind, node_id);
                    surface::visit::walk_ty(this, ty);
                });
            }
            surface::TyKind::GeneralExists { .. } => {
                self.with_scope(ScopeKind::Misc, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            surface::TyKind::Array(..) => {
                self.with_scope(ScopeKind::Misc, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            _ => surface::visit::walk_ty(self, ty),
        }
    }

    fn visit_bty(&mut self, bty: &surface::BaseTy) {
        match &bty.kind {
            surface::BaseTyKind::Slice(_) => {
                self.with_scope(ScopeKind::Misc, |this| {
                    surface::visit::walk_bty(this, bty);
                });
            }
            surface::BaseTyKind::Path(_) => {
                surface::visit::walk_bty(self, bty);
            }
        }
    }

    fn visit_expr(&mut self, expr: &surface::Expr) {
        match &expr.kind {
            surface::ExprKind::Path(path) => {
                self.on_path(path);
            }
            surface::ExprKind::App(func, _) => {
                self.on_func(*func, expr.node_id);
            }
            surface::ExprKind::Dot(path, _) => self.on_path(path),
            _ => {}
        }
        surface::visit::walk_expr(self, expr);
    }

    fn visit_base_sort(&mut self, bsort: &surface::BaseSort) {
        self.on_base_sort(bsort);
        surface::visit::walk_base_sort(self, bsort);
    }
}

struct ImplicitParamCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    path_res_map: &'a UnordMap<surface::NodeId, fhir::Res>,
    kind: ScopeKind,
    params: Vec<(Ident, fhir::ParamKind, NodeId)>,
}

impl<'a, 'tcx> ImplicitParamCollector<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        path_res_map: &'a UnordMap<surface::NodeId, fhir::Res>,
        kind: ScopeKind,
    ) -> Self {
        Self { tcx, path_res_map, kind, params: vec![] }
    }

    fn run(
        self,
        f: impl FnOnce(&mut ScopedVisitorWrapper<Self>),
    ) -> Vec<(Ident, fhir::ParamKind, NodeId)> {
        let mut wrapped = self.wrap();
        f(&mut wrapped);
        wrapped.0.params
    }
}

impl ScopedVisitor for ImplicitParamCollector<'_, '_> {
    fn is_box(&self, path: &surface::Path) -> bool {
        let res = self.path_res_map[&path.node_id];
        res.is_box(self.tcx)
    }

    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()> {
        if self.kind == kind {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }

    fn on_implicit_param(&mut self, ident: Ident, param: fhir::ParamKind, node_id: NodeId) {
        self.params.push((ident, param, node_id));
    }
}

struct Scope {
    kind: ScopeKind,
    bindings: FxIndexMap<Ident, ParamRes>,
}

impl Scope {
    fn new(kind: ScopeKind) -> Self {
        Self { kind, bindings: Default::default() }
    }
}

#[derive(Clone, Copy)]
struct ParamDef {
    ident: Ident,
    kind: fhir::ParamKind,
    scope: Option<NodeId>,
}

fn self_res(tcx: TyCtxt, owner: OwnerId) -> Option<fhir::SortRes> {
    let def_id = owner.def_id.to_def_id();
    let mut opt_def_id = Some(def_id);
    while let Some(def_id) = opt_def_id {
        match tcx.def_kind(def_id) {
            DefKind::Trait => return Some(fhir::SortRes::SelfParam { trait_id: def_id }),
            DefKind::Impl { .. } => return Some(fhir::SortRes::SelfAlias { alias_to: def_id }),
            _ => {
                opt_def_id = tcx.opt_parent(def_id);
            }
        }
    }
    None
}

pub(crate) struct RefinementResolver<'a, 'genv, 'tcx> {
    scopes: Vec<Scope>,
    sorts_res: UnordMap<Symbol, fhir::SortRes>,
    param_defs: FxIndexMap<NodeId, ParamDef>,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    path_res_map: FxHashMap<NodeId, PathRes<NodeId>>,
    errors: ErrorCollector<'genv>,
}

impl<'a, 'genv, 'tcx> RefinementResolver<'a, 'genv, 'tcx> {
    pub(crate) fn for_flux_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        sort_params: &[Ident],
    ) -> Self {
        let sort_res = sort_params
            .iter()
            .enumerate()
            .map(|(i, v)| (v.name, fhir::SortRes::SortParam(i)))
            .collect();
        Self::new(resolver, sort_res)
    }

    pub(crate) fn for_rust_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner: OwnerId,
    ) -> Self {
        let tcx = resolver.genv.tcx();
        let generics = tcx.generics_of(owner);
        let mut sort_res: UnordMap<_, _> = generics
            .params
            .iter()
            .map(|p| (p.name, fhir::SortRes::TyParam(p.def_id)))
            .collect();
        if let Some(self_res) = self_res(tcx, owner) {
            sort_res.insert(kw::SelfUpper, self_res);
        }
        Self::new(resolver, sort_res)
    }

    pub(crate) fn resolve_qualifier(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        qualifier: &surface::Qualifier,
    ) -> Result {
        Self::for_flux_item(resolver, &[]).run(|r| r.visit_qualifier(qualifier))
    }

    pub(crate) fn resolve_defn(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        defn: &surface::SpecFunc,
    ) -> Result {
        Self::for_flux_item(resolver, &defn.sort_vars).run(|r| r.visit_defn(defn))
    }

    pub(crate) fn resolve_fn_sig(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        fn_sig: &surface::FnSig,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_fn_sig(fn_sig))?;
        Self::for_rust_item(resolver, owner_id).run(|vis| vis.visit_fn_sig(fn_sig))
    }

    pub(crate) fn resolve_struct_def(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        struct_def: &surface::StructDef,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_struct_def(struct_def))?;
        Self::for_rust_item(resolver, owner_id).run(|vis| vis.visit_struct_def(struct_def))
    }

    pub(crate) fn resolve_enum_def(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        enum_def: &surface::EnumDef,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_enum_def(enum_def))?;
        Self::for_rust_item(resolver, owner_id).run(|vis| vis.visit_enum_def(enum_def))
    }

    pub(crate) fn resolve_ty_alias(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        ty_alias: &surface::TyAlias,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_ty_alias(ty_alias))?;
        Self::for_rust_item(resolver, owner_id).run(|vis| vis.visit_ty_alias(ty_alias))
    }

    pub(crate) fn resolve_impl(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        impl_: &surface::Impl,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_impl(impl_))?;
        Self::for_rust_item(resolver, owner_id).run(|vis| vis.visit_impl(impl_))
    }

    pub(crate) fn resolve_trait(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner_id: OwnerId,
        trait_: &surface::Trait,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_trait(trait_))?;
        Self::for_rust_item(resolver, owner_id).run(|vis| vis.visit_trait(trait_))
    }

    fn new(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        sort_res: UnordMap<Symbol, fhir::SortRes>,
    ) -> Self {
        let errors = ErrorCollector::new(resolver.genv.sess());
        Self {
            resolver,
            sorts_res: sort_res,
            param_defs: Default::default(),
            scopes: Default::default(),
            path_res_map: Default::default(),
            errors,
        }
    }

    fn run(self, f: impl FnOnce(&mut ScopedVisitorWrapper<Self>)) -> Result {
        let mut wrapper = self.wrap();
        f(&mut wrapper);
        wrapper.0.finish()
    }

    fn define_param(
        &mut self,
        ident: Ident,
        kind: fhir::ParamKind,
        param_id: NodeId,
        scope: Option<NodeId>,
    ) {
        self.param_defs
            .insert(param_id, ParamDef { ident, kind, scope });

        let scope = self.scopes.last_mut().unwrap();
        match scope.bindings.entry(ident) {
            IndexEntry::Occupied(entry) => {
                let param_def = self.param_defs[&entry.get().param_id()];
                self.errors
                    .emit(errors::DuplicateParam::new(param_def.ident, ident));
            }
            IndexEntry::Vacant(entry) => {
                entry.insert(ParamRes(kind, param_id));
            }
        }
    }

    fn find(&mut self, ident: Ident) -> Option<ParamRes> {
        for scope in self.scopes.iter().rev() {
            if let Some(res) = scope.bindings.get(&ident) {
                return Some(*res);
            }

            if scope.kind.is_barrier() {
                return None;
            }
        }
        None
    }

    fn resolve_ident(&mut self, ident: Ident, node_id: NodeId) {
        if let Some(res) = self.find(ident) {
            if let fhir::ParamKind::Error = res.kind() {
                self.errors.emit(errors::InvalidUnrefinedParam::new(ident));
                return;
            }
            self.path_res_map
                .insert(node_id, PathRes::Param(res.kind(), res.param_id()));
            return;
        }
        if let Some(const_def_id) = self.resolver.consts.get(&ident.name) {
            self.path_res_map
                .insert(node_id, PathRes::Const(*const_def_id));
            return;
        }
        if let Some(decl) = self.resolver.func_decls.get(&ident.name) {
            self.path_res_map
                .insert(node_id, PathRes::GlobalFunc(*decl, ident.name));
            return;
        }
        self.errors
            .emit(errors::UnresolvedVar::from_ident(ident, "name"));
    }

    fn resolve_sort_path(&mut self, path: &surface::SortPath) {
        let segment = path.segment;
        let res = if segment.name == SORTS.int {
            fhir::SortRes::PrimSort(fhir::PrimSort::Int)
        } else if segment.name == sym::bool {
            fhir::SortRes::PrimSort(fhir::PrimSort::Bool)
        } else if segment.name == SORTS.real {
            fhir::SortRes::PrimSort(fhir::PrimSort::Real)
        } else if segment.name == SORTS.set {
            fhir::SortRes::PrimSort(fhir::PrimSort::Set)
        } else if segment.name == SORTS.map {
            fhir::SortRes::PrimSort(fhir::PrimSort::Map)
        } else if let Some(res) = self.sorts_res.get(&segment.name) {
            *res
        } else if self.resolver.sort_decls.get(&segment.name).is_some() {
            fhir::SortRes::User { name: segment.name }
        } else if let Some(hir::def::Res::Def(
            DefKind::Struct | DefKind::Enum | DefKind::TyAlias,
            def_id,
        )) = self.resolver.resolve_ident(segment)
        {
            fhir::SortRes::Adt(def_id)
        } else {
            self.errors.emit(errors::UnresolvedSort::new(segment));
            return;
        };
        self.resolver
            .output
            .sort_path_res_map
            .insert(path.node_id, res);
    }

    pub(crate) fn finish(self) -> Result {
        let name_gen: IndexGen<fhir::Name> = IndexGen::new();
        let mut params = FxIndexMap::default();
        let mut name_for_param =
            |param_id| *params.entry(param_id).or_insert_with(|| name_gen.fresh());

        for (node_id, res) in self.path_res_map {
            let res = match res {
                PathRes::Param(kind, param_id) => PathRes::Param(kind, name_for_param(param_id)),
                PathRes::Const(def_id) => PathRes::Const(def_id),
                PathRes::NumConst(val) => PathRes::NumConst(val),
                PathRes::GlobalFunc(kind, name) => PathRes::GlobalFunc(kind, name),
            };
            self.resolver.output.path_expr_res_map.insert(node_id, res);
        }

        for (param_id, param_def) in self.param_defs {
            let name = match param_def.kind {
                fhir::ParamKind::Colon => {
                    if let Some(name) = params.get(&param_id) {
                        *name
                    } else {
                        continue;
                    }
                }
                fhir::ParamKind::Error => {
                    continue;
                }
                _ => {
                    params
                        .get(&param_id)
                        .copied()
                        .unwrap_or_else(|| name_gen.fresh())
                }
            };
            let output = &mut self.resolver.output;
            output
                .param_res_map
                .insert(param_id, (name, param_def.kind));

            if let Some(scope) = param_def.scope {
                output
                    .implicit_params
                    .entry(scope)
                    .or_default()
                    .push((param_def.ident, param_id));
            }
        }
        self.errors.into_result()
    }

    fn resolver_output(&self) -> &ResolverOutput {
        &self.resolver.output
    }
}

impl<'genv> ScopedVisitor for RefinementResolver<'_, 'genv, '_> {
    fn is_box(&self, path: &surface::Path) -> bool {
        let res = self.resolver_output().path_res_map[&path.node_id];
        res.is_box(self.resolver.genv.tcx())
    }

    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()> {
        self.scopes.push(Scope::new(kind));
        ControlFlow::Continue(())
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn on_enum_variant(&mut self, variant: &surface::VariantDef) {
        let params = ImplicitParamCollector::new(
            self.resolver.genv.tcx(),
            &self.resolver.output.path_res_map,
            ScopeKind::Variant,
        )
        .run(|vis| vis.visit_variant(variant));
        for (ident, kind, node_id) in params {
            self.define_param(ident, kind, node_id, Some(variant.node_id));
        }
    }

    fn on_fn_sig(&mut self, fn_sig: &surface::FnSig) {
        let params = ImplicitParamCollector::new(
            self.resolver.genv.tcx(),
            &self.resolver.output.path_res_map,
            ScopeKind::FnInput,
        )
        .run(|vis| vis.visit_fn_sig(fn_sig));
        for (ident, kind, param_id) in params {
            self.define_param(ident, kind, param_id, Some(fn_sig.node_id));
        }
    }

    fn on_fn_output(&mut self, output: &surface::FnOutput) {
        let params = ImplicitParamCollector::new(
            self.resolver.genv.tcx(),
            &self.resolver.output.path_res_map,
            ScopeKind::FnOutput,
        )
        .run(|vis| vis.visit_fn_output(output));
        for (ident, kind, param_id) in params {
            self.define_param(ident, kind, param_id, Some(output.node_id));
        }
    }

    fn on_generic_param(&mut self, param: &surface::GenericParam) {
        let surface::GenericParamKind::Refine { .. } = &param.kind else { return };
        self.define_param(param.name, fhir::ParamKind::Explicit, param.node_id, None);
    }

    fn on_refine_param(&mut self, name: Ident, node_id: NodeId) {
        self.define_param(name, fhir::ParamKind::Explicit, node_id, None);
    }

    fn on_func(&mut self, func: Ident, node_id: NodeId) {
        self.resolve_ident(func, node_id);
    }

    fn on_loc(&mut self, loc: Ident, node_id: NodeId) {
        self.resolve_ident(loc, node_id);
    }

    fn on_path(&mut self, path: &surface::PathExpr) {
        match &path.segments[..] {
            [var] => {
                self.resolve_ident(*var, path.node_id);
            }
            [typ, name] => {
                if let Some(res) = resolve_num_const(*typ, *name) {
                    self.resolver
                        .output
                        .path_expr_res_map
                        .insert(path.node_id, res);
                } else {
                    self.errors
                        .emit(errors::UnresolvedVar::from_path(path, "path"));
                }
            }
            _ => {
                self.errors
                    .emit(errors::UnresolvedVar::from_path(path, "path"));
            }
        }
    }

    fn on_base_sort(&mut self, sort: &surface::BaseSort) {
        match sort {
            surface::BaseSort::Path(path) => {
                self.resolve_sort_path(path);
            }
            surface::BaseSort::BitVec(_) => {}
        }
    }
}

macro_rules! define_resolve_num_const {
    ($($typ:ident),*) => {
        fn resolve_num_const(typ: surface::Ident, name: surface::Ident) -> Option<PathRes> {
            match typ.name.as_str() {
                $(
                    stringify!($typ) => {
                        match name.name.as_str() {
                            "MAX" => Some(PathRes::NumConst($typ::MAX.try_into().unwrap())),
                            "MIN" => Some(PathRes::NumConst($typ::MIN.try_into().unwrap())),
                            _ => None,
                        }
                    },
                )*
                _ => None
            }
        }
    };
}

define_resolve_num_const!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);

pub(crate) struct Sorts {
    pub int: Symbol,
    pub real: Symbol,
    pub set: Symbol,
    pub map: Symbol,
}

pub(crate) static SORTS: std::sync::LazyLock<Sorts> = std::sync::LazyLock::new(|| {
    Sorts {
        int: Symbol::intern("int"),
        real: Symbol::intern("real"),
        set: Symbol::intern("Set"),
        map: Symbol::intern("Map"),
    }
});

struct IllegalBinderVisitor<'a, 'genv, 'tcx> {
    scopes: Vec<ScopeKind>,
    resolver: &'a CrateResolver<'genv, 'tcx>,
    errors: ErrorCollector<'genv>,
}

impl<'a, 'genv, 'tcx> IllegalBinderVisitor<'a, 'genv, 'tcx> {
    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>) -> Self {
        let errors = ErrorCollector::new(resolver.genv.sess());
        Self { scopes: vec![], resolver, errors }
    }

    fn run(self, f: impl FnOnce(&mut ScopedVisitorWrapper<Self>)) -> Result {
        let mut vis = self.wrap();
        f(&mut vis);
        vis.0.errors.into_result()
    }
}

impl ScopedVisitor for IllegalBinderVisitor<'_, '_, '_> {
    fn is_box(&self, path: &surface::Path) -> bool {
        let res = self.resolver.output.path_res_map[&path.node_id];
        res.is_box(self.resolver.genv.tcx())
    }

    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()> {
        self.scopes.push(kind);
        ControlFlow::Continue(())
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn on_implicit_param(&mut self, ident: Ident, param_kind: fhir::ParamKind, _: NodeId) {
        let Some(scope_kind) = self.scopes.last() else { return };
        let (allowed, bind_kind) = match param_kind {
            fhir::ParamKind::At => {
                (
                    matches!(scope_kind, ScopeKind::FnInput | ScopeKind::Variant),
                    surface::BindKind::At,
                )
            }
            fhir::ParamKind::Pound => {
                (matches!(scope_kind, ScopeKind::FnOutput), surface::BindKind::Pound)
            }
            fhir::ParamKind::Colon
            | fhir::ParamKind::Loc(_)
            | fhir::ParamKind::Error
            | fhir::ParamKind::Explicit => return,
        };
        if !allowed {
            self.errors
                .emit(errors::IllegalBinder::new(ident.span, bind_kind));
        }
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use itertools::Itertools;
    use rustc_span::{symbol::Ident, Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(desugar_duplicate_param, code = "FLUX")]
    pub(super) struct DuplicateParam {
        #[primary_span]
        #[label]
        span: Span,
        name: Symbol,
        #[label(desugar_first_use)]
        first_use: Span,
    }

    impl DuplicateParam {
        pub(super) fn new(old_ident: Ident, new_ident: Ident) -> Self {
            debug_assert_eq!(old_ident.name, new_ident.name);
            Self { span: new_ident.span, name: new_ident.name, first_use: old_ident.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_sort, code = "FLUX")]
    pub(super) struct UnresolvedSort {
        #[primary_span]
        #[label]
        span: Span,
        sort: Ident,
    }

    impl UnresolvedSort {
        pub(super) fn new(sort: Ident) -> Self {
            Self { span: sort.span, sort }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_var, code = "FLUX")]
    pub(super) struct UnresolvedVar {
        #[primary_span]
        #[label]
        span: Span,
        var: String,
        kind: String,
    }

    impl UnresolvedVar {
        pub(super) fn from_path(path: &surface::PathExpr, kind: &str) -> Self {
            Self::from_segments(&path.segments, kind, path.span)
        }

        pub(super) fn from_ident(ident: Ident, kind: &str) -> Self {
            Self { span: ident.span, kind: kind.to_string(), var: format!("{ident}") }
        }

        fn from_segments(segments: &[Ident], kind: &str, span: Span) -> Self {
            Self {
                span,
                kind: kind.to_string(),
                var: format!("{}", segments.iter().format_with("::", |s, f| f(&s.name))),
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_invalid_unrefined_param, code = "FLUX")]
    pub(super) struct InvalidUnrefinedParam {
        #[primary_span]
        #[label]
        span: Span,
        var: Ident,
    }

    impl InvalidUnrefinedParam {
        pub(super) fn new(var: Ident) -> Self {
            Self { var, span: var.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_illegal_binder, code = "FLUX")]
    pub(super) struct IllegalBinder {
        #[primary_span]
        #[label]
        span: Span,
        kind: &'static str,
    }

    impl IllegalBinder {
        pub(super) fn new(span: Span, kind: surface::BindKind) -> Self {
            Self { span, kind: kind.token_str() }
        }
    }
}
