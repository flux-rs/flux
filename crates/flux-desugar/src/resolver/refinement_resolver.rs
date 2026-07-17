use std::ops::ControlFlow;

use flux_common::index::IndexGen;
use flux_errors::Errors;
use flux_middle::{
    ResolverOutput,
    fhir::{
        self,
        Namespace::{ReftNS, TypeNS, ValueNS},
        PartialRes, Res,
    },
};
use flux_syntax::{
    surface::{self, FluxItem, Ident, NodeId, visit::Visitor as _},
    walk_list,
};
use itertools::Itertools;
use rustc_data_structures::{fx::FxIndexMap, unord::UnordMap};
use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::{ErrorGuaranteed, Span};

use super::{CrateResolver, RibKind, Segment};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) trait ScopedVisitor: Sized {
    fn is_box(&self, segment: &surface::PathSegment) -> bool;
    fn enter_scope(&mut self, kind: RibKind) -> ControlFlow<()>;
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
    fn with_scope(&mut self, kind: RibKind, f: impl FnOnce(&mut Self)) {
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
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_trait_assoc_reft(this, assoc_reft);
        });
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &surface::ImplAssocReft) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_impl_assoc_reft(this, assoc_reft);
        });
    }

    fn visit_qualifier(&mut self, qualifier: &surface::Qualifier) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_qualifier(this, qualifier);
        });
    }

    fn visit_defn(&mut self, defn: &surface::SpecFunc) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_defn(this, defn);
        });
    }

    fn visit_primop_prop(&mut self, prop: &surface::PrimOpProp) {
        self.with_scope(RibKind::Misc, |this| {
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
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_ty_alias(this, ty_alias);
        });
    }

    fn visit_struct_def(&mut self, struct_def: &surface::StructDef) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_struct_def(this, struct_def);
        });
    }

    fn visit_enum_def(&mut self, enum_def: &surface::EnumDef) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_enum_def(this, enum_def);
        });
    }

    fn visit_variant(&mut self, variant: &surface::VariantDef) {
        self.with_scope(RibKind::Variant, |this| {
            this.on_enum_variant(variant);
            surface::visit::walk_variant(this, variant);
        });
    }

    fn visit_trait_ref(&mut self, trait_ref: &surface::TraitRef) {
        match trait_ref.as_fn_trait_ref() {
            Some((in_arg, out_arg)) => {
                self.with_scope(RibKind::FnTraitInput, |this| {
                    this.on_fn_trait_input(in_arg, trait_ref.node_id);
                    surface::visit::walk_generic_arg(this, in_arg);
                    this.with_scope(RibKind::Misc, |this| {
                        surface::visit::walk_generic_arg(this, out_arg);
                    });
                });
            }
            None => {
                self.with_scope(RibKind::Misc, |this| {
                    surface::visit::walk_trait_ref(this, trait_ref);
                });
            }
        }
    }

    fn visit_variant_ret(&mut self, ret: &surface::VariantRet) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_variant_ret(this, ret);
        });
    }

    fn visit_generics(&mut self, generics: &surface::Generics) {
        self.with_scope(RibKind::Misc, |this| {
            surface::visit::walk_generics(this, generics);
        });
    }

    fn visit_fn_sig(&mut self, fn_sig: &surface::FnSig) {
        self.with_scope(RibKind::FnInput, |this| {
            this.on_fn_sig(fn_sig);
            surface::visit::walk_fn_sig(this, fn_sig);
        });
    }

    fn visit_fn_output(&mut self, output: &surface::FnOutput) {
        self.with_scope(RibKind::FnOutput, |this| {
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
                self.with_scope(RibKind::Misc, |this| {
                    surface::visit::walk_refine_arg(this, arg);
                });
            }
            surface::RefineArg::Expr(expr) => self.visit_expr(expr),
        }
    }

    fn visit_path(&mut self, path: &surface::Path) {
        for arg in &path.refine {
            self.with_scope(RibKind::Misc, |this| this.visit_refine_arg(arg));
        }
        walk_list!(self, visit_path_segment, &path.segments);
    }

    fn visit_path_segment(&mut self, segment: &surface::PathSegment) {
        let is_box = self.is_box(segment);
        for (i, arg) in segment.args.iter().enumerate() {
            if is_box && i == 0 {
                self.visit_generic_arg(arg);
            } else {
                self.with_scope(RibKind::Misc, |this| this.visit_generic_arg(arg));
            }
        }
    }

    fn visit_ty(&mut self, ty: &surface::Ty) {
        let node_id = ty.node_id;
        match &ty.kind {
            surface::TyKind::Exists { bind, .. } => {
                self.with_scope(RibKind::Misc, |this| {
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
                self.with_scope(RibKind::Misc, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            surface::TyKind::Array(..) => {
                self.with_scope(RibKind::Misc, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            _ => surface::visit::walk_ty(self, ty),
        }
    }

    fn visit_bty(&mut self, bty: &surface::BaseTy) {
        match &bty.kind {
            surface::BaseTyKind::Slice(_) | surface::BaseTyKind::Ptr(..) => {
                self.with_scope(RibKind::Misc, |this| {
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
    path_res_map: &'a UnordMap<surface::NodeId, fhir::PartialRes<NodeId>>,
    kind: RibKind,
    params: Vec<(Ident, fhir::ParamKind, NodeId)>,
}

impl<'a, 'tcx> ImplicitParamCollector<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        path_res_map: &'a UnordMap<surface::NodeId, fhir::PartialRes<NodeId>>,
        kind: RibKind,
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

    fn enter_scope(&mut self, kind: RibKind) -> ControlFlow<()> {
        if self.kind == kind { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
    }

    fn on_implicit_param(&mut self, ident: Ident, param: fhir::ParamKind, node_id: NodeId) {
        self.params.push((ident, param, node_id));
    }
}

#[derive(Clone, Copy)]
struct ParamDef {
    ident: Ident,
    kind: fhir::ParamKind,
    scope: Option<NodeId>,
}

pub(crate) struct RefinementResolver<'a, 'genv, 'tcx> {
    param_defs: FxIndexMap<NodeId, ParamDef>,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    path_res_map: FxHashMap<NodeId, PartialRes<NodeId>>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> RefinementResolver<'a, 'genv, 'tcx> {
    pub(crate) fn resolve_flux_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &FluxItem,
    ) -> Result {
        let sort_vars = match item {
            FluxItem::FuncDef(defn) => &defn.sort_vars[..],
            FluxItem::SortDecl(sort_decl) => &sort_decl.sort_vars[..],
            FluxItem::Qualifier(_) | FluxItem::PrimOpProp(_) => &[],
        };
        Self::new(resolver).run(sort_vars, |r| r.visit_flux_item(item))
    }

    pub(crate) fn resolve_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &surface::Item,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_item(item))?;
        Self::new(resolver).run(&[], |vis| vis.visit_item(item))
    }

    pub(crate) fn resolve_trait_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &surface::TraitItemFn,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_trait_item(item))?;
        Self::new(resolver).run(&[], |vis| vis.visit_trait_item(item))
    }

    pub(crate) fn resolve_impl_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &surface::ImplItemFn,
    ) -> Result {
        IllegalBinderVisitor::new(resolver).run(|vis| vis.visit_impl_item(item))?;
        Self::new(resolver).run(&[], |vis| vis.visit_impl_item(item))
    }

    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>) -> Self {
        let errors = Errors::new(resolver.genv.sess());
        Self { resolver, param_defs: Default::default(), path_res_map: Default::default(), errors }
    }

    fn run(self, sort_vars: &[Ident], f: impl FnOnce(&mut ScopedVisitorWrapper<Self>)) -> Result {
        // Sort variables share the type namespace with sorts/types (see [`fhir::Namespace`]).
        self.resolver.push_rib(TypeNS, RibKind::Misc);
        for (idx, ident) in sort_vars.iter().enumerate() {
            self.resolver
                .define_res_in(ident.name, Res::SortParam(idx), TypeNS);
        }
        let mut wrapper = self.wrap();
        f(&mut wrapper);
        wrapper.resolver.pop_rib(TypeNS);

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

        if let Some(Res::Param(_, prev_id)) =
            self.resolver
                .define_res_in(ident.name, Res::Param(kind, param_id), ReftNS)
        {
            let prev_ident = self.param_defs[&prev_id].ident;
            self.errors
                .emit(errors::DuplicateParam::new(prev_ident, ident));
        }
    }

    fn resolve_path(&mut self, path: &surface::ExprPath) {
        if let Some(res) = self.try_resolve_expr_with_ribs(&path.segments) {
            self.check_unrefined_param(res, path.segments.last().unwrap().ident);
            self.path_res_map.insert(path.node_id, res);
            return;
        }

        self.emit_unresolved_expr_path(path);
    }

    fn resolve_ident(&mut self, ident: Ident, node_id: NodeId) {
        if let Some(res) = self.try_resolve_expr_with_ribs(&[ident]) {
            self.check_unrefined_param(res, ident);
            self.path_res_map.insert(node_id, res);
            return;
        }
        self.emit_unresolved_ident(ident);
    }

    /// Emit an error if `res` resolved to a param that cannot be refined.
    /// e.g., `fn(x: &mut i32) -> i32[x]`
    fn check_unrefined_param(&mut self, res: PartialRes<NodeId>, ident: Ident) {
        if let Some(Res::Param(fhir::ParamKind::Error, _)) = res.full_res() {
            self.errors.emit(errors::InvalidUnrefinedParam::new(ident));
        }
    }

    fn try_resolve_expr_with_ribs<S: Segment>(
        &mut self,
        segments: &[S],
    ) -> Option<PartialRes<NodeId>> {
        // Try the refinement namespace first so that refinement params (and then flux funcs) take
        // precedence over Rust value/type bindings — in particular, a param shadows a Rust const of
        // the same name.
        for ns in [ReftNS, ValueNS, TypeNS] {
            if let Some(partial_res) = self.resolver.resolve_path_with_ribs(segments, ns) {
                return Some(partial_res);
            }
        }
        None
    }

    fn resolve_sort_path(&mut self, path: &surface::SortPath) {
        // Sorts resolve in the type namespace: primitive/user sorts and sort parameters live there
        // alongside types, and any type can also denote a sort. We only report a *name* that fails
        // to resolve here; whether the resolved item is admissible as a sort (and the corresponding
        // diagnostic) is decided later in `conv_sort_path`.
        let res = self
            .resolver
            .resolve_path_with_ribs(&path.segments, TypeNS)
            .unwrap_or_else(|| {
                self.emit_unresolved_sort_path(path);
                PartialRes::new(fhir::Res::Err)
            });
        self.resolver.output.path_res_map.insert(path.node_id, res);
    }

    pub(crate) fn finish(self) -> Result {
        let param_id_gen = IndexGen::new();
        let mut params = FxIndexMap::default();

        // Create an `fhir::ParamId` for all parameters used in a path before iterating over
        // `param_defs` such that we can skip `fhir::ParamKind::Colon` if the param wasn't used
        for (node_id, res) in self.path_res_map {
            self.resolver.output.path_res_map.insert(node_id, res);
            if let Res::Param(_, param_id) = res.base_res() {
                params
                    .entry(param_id)
                    .or_insert_with(|| param_id_gen.fresh());
            }
        }

        // At this point, the `params` map contains all parameters that were used in an expression,
        // so we can safely skip `ParamKind::Colon` if there's no entry for it.
        for (node_id, param_def) in self.param_defs {
            let param_id = match param_def.kind {
                fhir::ParamKind::Colon => {
                    let Some(param_id) = params.get(&node_id) else { continue };
                    *param_id
                }
                fhir::ParamKind::Error => continue,
                _ => {
                    params
                        .get(&node_id)
                        .copied()
                        .unwrap_or_else(|| param_id_gen.fresh())
                }
            };
            let output = &mut self.resolver.output;
            output
                .param_res_map
                .insert(node_id, (param_id, param_def.kind));

            if let Some(scope) = param_def.scope {
                output
                    .implicit_params
                    .entry(scope)
                    .or_default()
                    .push((param_def.ident, node_id));
            }
        }
        self.errors.to_result()
    }

    fn resolver_output(&self) -> &ResolverOutput {
        &self.resolver.output
    }

    fn emit_unresolved_ident(&mut self, ident: Ident) {
        self.errors.emit(super::errors::UnresolvedName {
            span: ident.span,
            name: ident.to_string(),
            kind: "value",
        });
    }

    fn emit_unresolved_expr_path(&mut self, path: &surface::ExprPath) {
        self.errors.emit(super::errors::UnresolvedName {
            span: path.span,
            name: path.segments.iter().map(|s| s.ident).join("::"),
            kind: "value",
        });
    }

    fn emit_unresolved_sort_path(&mut self, path: &surface::SortPath) {
        self.errors.emit(super::errors::UnresolvedName {
            span: path
                .segments
                .iter()
                .map(|ident| ident.span)
                .reduce(Span::to)
                .unwrap_or_default(),
            name: path.segments.iter().join("::"),
            kind: "sort",
        });
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

    fn enter_scope(&mut self, kind: RibKind) -> ControlFlow<()> {
        self.resolver.push_rib(ReftNS, kind);
        ControlFlow::Continue(())
    }

    fn exit_scope(&mut self) {
        self.resolver.pop_rib(ReftNS);
    }

    fn on_fn_trait_input(&mut self, in_arg: &surface::GenericArg, trait_node_id: NodeId) {
        let params = ImplicitParamCollector::new(
            self.resolver.genv.tcx(),
            &self.resolver.output.path_res_map,
            RibKind::FnTraitInput,
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
            RibKind::Variant,
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
            RibKind::FnInput,
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
            RibKind::FnOutput,
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
            surface::BaseSort::Tuple(sorts) => {
                for sort in sorts {
                    self.on_base_sort(sort);
                }
            }
        }
    }
}

struct IllegalBinderVisitor<'a, 'genv, 'tcx> {
    scopes: Vec<RibKind>,
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
        vis.0.errors.to_result()
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

    fn enter_scope(&mut self, kind: RibKind) -> ControlFlow<()> {
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
                        RibKind::FnInput | RibKind::FnTraitInput | RibKind::Variant
                    ),
                    surface::BindKind::At,
                )
            }
            fhir::ParamKind::Pound => {
                (matches!(scope_kind, RibKind::FnOutput), surface::BindKind::Pound)
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
