use std::ops::ControlFlow;

use flux_common::index::IndexGen;
use flux_errors::Errors;
use flux_middle::{
    ResolverOutput,
    fhir::{self, ExprRes},
};
use flux_syntax::{
    surface::{self, Ident, NodeId, visit::Visitor as _},
    symbols::sym,
    walk_list,
};
use rustc_data_structures::{
    fx::{FxIndexMap, FxIndexSet, IndexEntry},
    unord::UnordMap,
};
use rustc_hash::FxHashMap;
use rustc_hir::def::{
    DefKind,
    Namespace::{TypeNS, ValueNS},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{ErrorGuaranteed, Symbol};

use super::{CrateResolver, Segment};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ScopeKind {
    FnInput,
    FnOutput,
    Variant,
    Misc,
    FnTraitInput,
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
    fn is_box(&self, segment: &surface::PathSegment) -> bool;
    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()>;
    fn exit_scope(&mut self) {}

    fn wrap(self) -> ScopedVisitorWrapper<Self> {
        ScopedVisitorWrapper(self)
    }

    fn on_implicit_param(&mut self, _ident: Ident, _kind: fhir::ParamKind, _node_id: NodeId) {}
    fn on_generic_param(&mut self, _param: &surface::GenericParam) {}
    fn on_refine_param(&mut self, _param: &surface::RefineParam) {}
    fn on_enum_variant(&mut self, _variant: &surface::VariantDef) {}
    fn on_fn_trait_input(&mut self, _in_arg: &surface::GenericArg, _node_id: NodeId) {}
    fn on_fn_sig(&mut self, _fn_sig: &surface::FnSig) {}
    fn on_fn_output(&mut self, _output: &surface::FnOutput) {}
    fn on_loc(&mut self, _loc: Ident, _node_id: NodeId) {}
    fn on_path(&mut self, _path: &surface::ExprPath) {}
    fn on_base_sort(&mut self, _sort: &surface::BaseSort) {}
}

pub(crate) struct ScopedVisitorWrapper<V>(V);

impl<V: ScopedVisitor> ScopedVisitorWrapper<V> {
    fn with_scope(&mut self, kind: ScopeKind, f: impl FnOnce(&mut Self)) {
        let scope = self.0.enter_scope(kind);
        if let ControlFlow::Continue(_) = scope {
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

    fn visit_primop_prop(&mut self, prop: &surface::PrimOpProp) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_primop_prop(this, prop);
        });
    }

    fn visit_generic_param(&mut self, param: &surface::GenericParam) {
        self.on_generic_param(param);
        surface::visit::walk_generic_param(self, param);
    }

    fn visit_refine_param(&mut self, param: &surface::RefineParam) {
        self.on_refine_param(param);
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

    fn visit_trait_ref(&mut self, trait_ref: &surface::TraitRef) {
        match trait_ref.as_fn_trait_ref() {
            Some((in_arg, out_arg)) => {
                self.with_scope(ScopeKind::FnTraitInput, |this| {
                    this.on_fn_trait_input(in_arg, trait_ref.node_id);
                    surface::visit::walk_generic_arg(this, in_arg);
                    this.with_scope(ScopeKind::Misc, |this| {
                        surface::visit::walk_generic_arg(this, out_arg);
                    });
                });
            }
            None => {
                self.with_scope(ScopeKind::Misc, |this| {
                    surface::visit::walk_trait_ref(this, trait_ref);
                });
            }
        }
    }

    fn visit_variant_ret(&mut self, ret: &surface::VariantRet) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_variant_ret(this, ret);
        });
    }

    fn visit_generics(&mut self, generics: &surface::Generics) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_generics(this, generics);
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

    fn visit_fn_input(&mut self, arg: &surface::FnInput) {
        match arg {
            surface::FnInput::Constr(bind, _, _, node_id) => {
                self.on_implicit_param(*bind, fhir::ParamKind::Colon, *node_id);
            }
            surface::FnInput::StrgRef(loc, _, node_id) => {
                self.on_implicit_param(*loc, fhir::ParamKind::Loc, *node_id);
            }
            surface::FnInput::Ty(bind, ty, node_id) => {
                if let &Some(bind) = bind {
                    let param_kind = if let surface::TyKind::Base(_) = &ty.kind {
                        fhir::ParamKind::Colon
                    } else {
                        fhir::ParamKind::Error
                    };
                    self.on_implicit_param(bind, param_kind, *node_id);
                }
            }
        }
        surface::visit::walk_fn_input(self, arg);
    }

    fn visit_ensures(&mut self, constraint: &surface::Ensures) {
        if let surface::Ensures::Type(loc, _, node_id) = constraint {
            self.on_loc(*loc, *node_id);
        }
        surface::visit::walk_ensures(self, constraint);
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
        for arg in &path.refine {
            self.with_scope(ScopeKind::Misc, |this| this.visit_refine_arg(arg));
        }
        walk_list!(self, visit_path_segment, &path.segments);
    }

    fn visit_path_segment(&mut self, segment: &surface::PathSegment) {
        let is_box = self.is_box(segment);
        for (i, arg) in segment.args.iter().enumerate() {
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
                    let param = surface::RefineParam {
                        ident: *bind,
                        mode: None,
                        sort: surface::Sort::Infer,
                        node_id,
                        span: bind.span,
                    };
                    this.on_refine_param(&param);
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
            surface::BaseTyKind::Path(..) => {
                surface::visit::walk_bty(self, bty);
            }
        }
    }

    fn visit_path_expr(&mut self, path: &surface::ExprPath) {
        self.on_path(path);
    }

    fn visit_base_sort(&mut self, bsort: &surface::BaseSort) {
        self.on_base_sort(bsort);
        surface::visit::walk_base_sort(self, bsort);
    }
}

struct ImplicitParamCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    path_res_map: &'a UnordMap<surface::NodeId, fhir::PartialRes>,
    kind: ScopeKind,
    params: Vec<(Ident, fhir::ParamKind, NodeId)>,
}

impl<'a, 'tcx> ImplicitParamCollector<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        path_res_map: &'a UnordMap<surface::NodeId, fhir::PartialRes>,
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
    fn is_box(&self, segment: &surface::PathSegment) -> bool {
        self.path_res_map
            .get(&segment.node_id)
            .map(|r| r.is_box(self.tcx))
            .unwrap_or(false)
    }

    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()> {
        if self.kind == kind { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
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

pub(crate) struct RefinementResolver<'a, 'genv, 'tcx> {
    scopes: Vec<Scope>,
    sort_params: FxIndexSet<Symbol>,
    param_defs: FxIndexMap<NodeId, ParamDef>,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    path_res_map: FxHashMap<NodeId, ExprRes<NodeId>>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> RefinementResolver<'a, 'genv, 'tcx> {
    pub(crate) fn for_flux_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        sort_params: &[Ident],
    ) -> Self {
        Self::new(resolver, sort_params.iter().map(|ident| ident.name).collect())
    }

    pub(crate) fn for_rust_item(resolver: &'a mut CrateResolver<'genv, 'tcx>) -> Self {
        Self::new(resolver, Default::default())
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

    pub(crate) fn resolve_primop_prop(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        prop: &surface::PrimOpProp,
    ) -> Result {
        Self::for_flux_item(resolver, &[]).run(|r| r.visit_primop_prop(prop))
    }

    pub(crate) fn resolve_fn_sig(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        fn_sig: &surface::FnSig,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_fn_sig(fn_sig))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_fn_sig(fn_sig))
    }

    pub(crate) fn resolve_struct_def(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        struct_def: &surface::StructDef,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_struct_def(struct_def))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_struct_def(struct_def))
    }

    pub(crate) fn resolve_enum_def(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        enum_def: &surface::EnumDef,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_enum_def(enum_def))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_enum_def(enum_def))
    }

    pub(crate) fn resolve_constant(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        constant_info: &surface::ConstantInfo,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_constant(constant_info))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_constant(constant_info))
    }

    pub(crate) fn resolve_ty_alias(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        ty_alias: &surface::TyAlias,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_ty_alias(ty_alias))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_ty_alias(ty_alias))
    }

    pub(crate) fn resolve_impl(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        impl_: &surface::Impl,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_impl(impl_))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_impl(impl_))
    }

    pub(crate) fn resolve_trait(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        trait_: &surface::Trait,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_trait(trait_))?;
        Self::for_rust_item(resolver).run(|vis| vis.visit_trait(trait_))
    }

    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>, sort_params: FxIndexSet<Symbol>) -> Self {
        let errors = Errors::new(resolver.genv.sess());
        Self {
            resolver,
            sort_params,
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

    fn try_resolve_enum_variant(&mut self, typ: Ident, variant: Ident) -> Option<ExprRes<NodeId>> {
        if let fhir::Res::Def(_, enum_def_id) =
            self.resolver.resolve_ident_with_ribs(typ, TypeNS)?
        {
            let enum_variants = self.resolver.enum_variants.get(&enum_def_id)?;
            let variant_def_id = enum_variants.variants.get(&variant.name)?;
            return Some(ExprRes::Variant(*variant_def_id));
        }
        None
    }

    fn resolve_path(&mut self, path: &surface::ExprPath) {
        if let [segment] = &path.segments[..]
            && let Some(res) = self.try_resolve_param(segment.ident)
        {
            self.path_res_map.insert(path.node_id, res);
            return;
        }
        if let Some(res) = self.try_resolve_expr_with_ribs(&path.segments) {
            self.path_res_map.insert(path.node_id, res);
            return;
        }
        // TODO(nilehmann) move this to resolve_with_ribs
        if let [typ, name] = &path.segments[..]
            && let Some(res) = resolve_num_const(typ.ident, name.ident)
        {
            self.path_res_map.insert(path.node_id, res);
            return;
        }
        if let [typ, name] = &path.segments[..]
            && let Some(res) = self.try_resolve_enum_variant(typ.ident, name.ident)
        {
            self.path_res_map.insert(path.node_id, res);
            return;
        }
        if let [segment] = &path.segments[..]
            && let Some(res) = self.try_resolve_global_func(segment.ident)
        {
            self.path_res_map.insert(path.node_id, res);
            return;
        }

        self.errors.emit(errors::UnresolvedVar::from_path(path));
    }

    fn resolve_ident(&mut self, ident: Ident, node_id: NodeId) {
        if let Some(res) = self.try_resolve_param(ident) {
            self.path_res_map.insert(node_id, res);
            return;
        }
        if let Some(res) = self.try_resolve_expr_with_ribs(&[ident]) {
            self.path_res_map.insert(node_id, res);
            return;
        }
        if let Some(res) = self.try_resolve_global_func(ident) {
            self.path_res_map.insert(node_id, res);
            return;
        }
        self.errors.emit(errors::UnresolvedVar::from_ident(ident));
    }

    fn try_resolve_expr_with_ribs<S: Segment>(
        &mut self,
        segments: &[S],
    ) -> Option<ExprRes<NodeId>> {
        let path = self.resolver.resolve_path_with_ribs(segments, ValueNS);

        let res = match path {
            Some(r) => r.full_res()?,
            _ => {
                self.resolver
                    .resolve_path_with_ribs(segments, TypeNS)?
                    .full_res()?
            }
        };
        match res {
            fhir::Res::Def(DefKind::ConstParam, def_id) => Some(ExprRes::ConstGeneric(def_id)),
            fhir::Res::Def(DefKind::Const, def_id) => Some(ExprRes::Const(def_id)),
            fhir::Res::Def(DefKind::Struct | DefKind::Enum, def_id) => Some(ExprRes::Ctor(def_id)),
            fhir::Res::Def(DefKind::Variant, def_id) => Some(ExprRes::Variant(def_id)),
            _ => None,
        }
    }

    fn try_resolve_param(&mut self, ident: Ident) -> Option<ExprRes<NodeId>> {
        let res = self.find(ident)?;

        if let fhir::ParamKind::Error = res.kind() {
            self.errors.emit(errors::InvalidUnrefinedParam::new(ident));
        }
        Some(ExprRes::Param(res.kind(), res.param_id()))
    }

    fn try_resolve_global_func(&mut self, ident: Ident) -> Option<ExprRes<NodeId>> {
        let kind = self.resolver.func_decls.get(&ident.name)?;
        Some(ExprRes::GlobalFunc(*kind))
    }

    fn resolve_sort_path(&mut self, path: &surface::SortPath) {
        let res = self
            .try_resolve_sort_param(path)
            .or_else(|| self.try_resolve_sort_with_ribs(path))
            .or_else(|| self.try_resolve_user_sort(path))
            .or_else(|| self.try_resolve_prim_sort(path));

        if let Some(res) = res {
            self.resolver
                .output
                .sort_path_res_map
                .insert(path.node_id, res);
        } else {
            self.errors.emit(errors::UnresolvedSort::new(path));
        }
    }

    fn try_resolve_sort_param(&self, path: &surface::SortPath) -> Option<fhir::SortRes> {
        let [segment] = &path.segments[..] else { return None };
        self.sort_params
            .get_index_of(&segment.name)
            .map(fhir::SortRes::SortParam)
    }

    fn try_resolve_sort_with_ribs(&mut self, path: &surface::SortPath) -> Option<fhir::SortRes> {
        let partial_res = self
            .resolver
            .resolve_path_with_ribs(&path.segments, TypeNS)?;
        match (partial_res.base_res(), partial_res.unresolved_segments()) {
            (fhir::Res::Def(DefKind::Struct | DefKind::Enum, def_id), 0) => {
                Some(fhir::SortRes::Adt(def_id))
            }
            (fhir::Res::Def(DefKind::TyParam, def_id), 0) => Some(fhir::SortRes::TyParam(def_id)),
            (fhir::Res::SelfTyParam { trait_ }, 0) => {
                Some(fhir::SortRes::SelfParam { trait_id: trait_ })
            }
            (fhir::Res::SelfTyParam { trait_ }, 1) => {
                let ident = *path.segments.last().unwrap();
                Some(fhir::SortRes::SelfParamAssoc { trait_id: trait_, ident })
            }
            (fhir::Res::SelfTyAlias { alias_to, .. }, 0) => {
                Some(fhir::SortRes::SelfAlias { alias_to })
            }
            _ => None,
        }
    }

    fn try_resolve_user_sort(&self, path: &surface::SortPath) -> Option<fhir::SortRes> {
        let [segment] = &path.segments[..] else { return None };
        self.resolver
            .sort_decls
            .get(&segment.name)
            .map(|decl| fhir::SortRes::User { name: decl.name })
    }

    fn try_resolve_prim_sort(&self, path: &surface::SortPath) -> Option<fhir::SortRes> {
        let [segment] = &path.segments[..] else { return None };
        if segment.name == sym::int {
            Some(fhir::SortRes::PrimSort(fhir::PrimSort::Int))
        } else if segment.name == sym::bool {
            Some(fhir::SortRes::PrimSort(fhir::PrimSort::Bool))
        } else if segment.name == sym::char {
            Some(fhir::SortRes::PrimSort(fhir::PrimSort::Char))
        } else if segment.name == sym::real {
            Some(fhir::SortRes::PrimSort(fhir::PrimSort::Real))
        } else if segment.name == sym::Set {
            Some(fhir::SortRes::PrimSort(fhir::PrimSort::Set))
        } else if segment.name == sym::Map {
            Some(fhir::SortRes::PrimSort(fhir::PrimSort::Map))
        } else {
            None
        }
    }

    pub(crate) fn finish(self) -> Result {
        let param_id_gen = IndexGen::new();
        let mut params = FxIndexMap::default();

        // Create an `fhir::ParamId` for all parameters used in a path before iterating over
        // `param_defs` such that we can skip `fhir::ParamKind::Colon` if the param wasn't used
        for (node_id, res) in self.path_res_map {
            let res = res.map_param_id(|param_id| {
                *params
                    .entry(param_id)
                    .or_insert_with(|| param_id_gen.fresh())
            });
            self.resolver.output.expr_path_res_map.insert(node_id, res);
        }

        // At this point, the `params` map contains all parameters that were used in an expression,
        // so we can safely skip `ParamKind::Colon` if there's no entry for it.
        for (param_id, param_def) in self.param_defs {
            let name = match param_def.kind {
                fhir::ParamKind::Colon => {
                    let Some(name) = params.get(&param_id) else { continue };
                    *name
                }
                fhir::ParamKind::Error => continue,
                _ => {
                    params
                        .get(&param_id)
                        .copied()
                        .unwrap_or_else(|| param_id_gen.fresh())
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

impl ScopedVisitor for RefinementResolver<'_, '_, '_> {
    fn is_box(&self, segment: &surface::PathSegment) -> bool {
        self.resolver_output()
            .path_res_map
            .get(&segment.node_id)
            .map(|r| r.is_box(self.resolver.genv.tcx()))
            .unwrap_or(false)
    }

    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()> {
        self.scopes.push(Scope::new(kind));
        ControlFlow::Continue(())
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn on_fn_trait_input(&mut self, in_arg: &surface::GenericArg, trait_node_id: NodeId) {
        let params = ImplicitParamCollector::new(
            self.resolver.genv.tcx(),
            &self.resolver.output.path_res_map,
            ScopeKind::FnTraitInput,
        )
        .run(|vis| vis.visit_generic_arg(in_arg));
        for (ident, kind, node_id) in params {
            self.define_param(ident, kind, node_id, Some(trait_node_id));
        }
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

    fn on_refine_param(&mut self, param: &surface::RefineParam) {
        self.define_param(param.ident, fhir::ParamKind::Explicit(param.mode), param.node_id, None);
    }

    fn on_loc(&mut self, loc: Ident, node_id: NodeId) {
        self.resolve_ident(loc, node_id);
    }

    fn on_path(&mut self, path: &surface::ExprPath) {
        self.resolve_path(path);
    }

    fn on_base_sort(&mut self, sort: &surface::BaseSort) {
        match sort {
            surface::BaseSort::Path(path) => {
                self.resolve_sort_path(path);
            }
            surface::BaseSort::BitVec(_) => {}
            surface::BaseSort::SortOf(..) => {}
        }
    }
}

macro_rules! define_resolve_num_const {
    ($($typ:ident),*) => {
        fn resolve_num_const(typ: surface::Ident, name: surface::Ident) -> Option<ExprRes<NodeId>> {
            match typ.name.as_str() {
                $(
                    stringify!($typ) => {
                        match name.name.as_str() {
                            "MAX" => Some(ExprRes::NumConst($typ::MAX.try_into().unwrap())),
                            "MIN" => Some(ExprRes::NumConst($typ::MIN.try_into().unwrap())),
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

struct IllegalBinderVisitor<'a, 'genv, 'tcx> {
    scopes: Vec<ScopeKind>,
    resolver: &'a CrateResolver<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> IllegalBinderVisitor<'a, 'genv, 'tcx> {
    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>) -> Self {
        let errors = Errors::new(resolver.genv.sess());
        Self { scopes: vec![], resolver, errors }
    }

    fn run(self, f: impl FnOnce(&mut ScopedVisitorWrapper<Self>)) -> Result {
        let mut vis = self.wrap();
        f(&mut vis);
        vis.0.errors.into_result()
    }
}

impl ScopedVisitor for IllegalBinderVisitor<'_, '_, '_> {
    fn is_box(&self, segment: &surface::PathSegment) -> bool {
        self.resolver
            .output
            .path_res_map
            .get(&segment.node_id)
            .map(|r| r.is_box(self.resolver.genv.tcx()))
            .unwrap_or(false)
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
                    matches!(
                        scope_kind,
                        ScopeKind::FnInput | ScopeKind::FnTraitInput | ScopeKind::Variant
                    ),
                    surface::BindKind::At,
                )
            }
            fhir::ParamKind::Pound => {
                (matches!(scope_kind, ScopeKind::FnOutput), surface::BindKind::Pound)
            }
            fhir::ParamKind::Colon
            | fhir::ParamKind::Loc
            | fhir::ParamKind::Error
            | fhir::ParamKind::Explicit(..) => return,
        };
        if !allowed {
            self.errors
                .emit(errors::IllegalBinder::new(ident.span, bind_kind));
        }
    }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use itertools::Itertools;
    use rustc_span::{Span, Symbol, symbol::Ident};

    #[derive(Diagnostic)]
    #[diag(desugar_duplicate_param, code = E0999)]
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
    #[diag(desugar_unresolved_sort, code = E0999)]
    pub(super) struct UnresolvedSort {
        #[primary_span]
        #[label]
        span: Span,
        name: String,
    }

    impl UnresolvedSort {
        pub(super) fn new(path: &surface::SortPath) -> Self {
            Self {
                span: path
                    .segments
                    .iter()
                    .map(|ident| ident.span)
                    .reduce(Span::to)
                    .unwrap_or_default(),
                name: format!("{}", path.segments.iter().format("::")),
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_var, code = E0999)]
    pub(super) struct UnresolvedVar {
        #[primary_span]
        #[label]
        span: Span,
        var: String,
    }

    impl UnresolvedVar {
        pub(super) fn from_path(path: &surface::ExprPath) -> Self {
            Self {
                span: path.span,
                var: format!(
                    "{}",
                    path.segments
                        .iter()
                        .format_with("::", |s, f| f(&s.ident.name))
                ),
            }
        }

        pub(super) fn from_ident(ident: Ident) -> Self {
            Self { span: ident.span, var: format!("{ident}") }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_invalid_unrefined_param, code = E0999)]
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
    #[diag(desugar_illegal_binder, code = E0999)]
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
