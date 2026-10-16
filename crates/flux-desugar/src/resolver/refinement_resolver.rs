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
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{UnordMap, UnordSet},
};
use rustc_span::{ErrorGuaranteed, Span};

use super::{BindingSource, CrateResolver, ResolveError, RibKind, Segment};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) trait ScopedVisitor: Sized {
    fn is_box(&self, segment: &surface::PathSegment) -> bool;
    /// `node_id` is the [`NodeId`] of the node that owns the implicit params bound directly in
    /// this scope. It is `Some` for the scopes where implicit params can be bound, i.e., fn inputs,
    /// fn outputs, variants, fn pointer inputs and fn trait inputs.
    fn enter_scope(&mut self, kind: RibKind, node_id: Option<NodeId>);
    fn exit_scope(&mut self);

    fn wrap(self) -> ScopedVisitorWrapper<Self> {
        ScopedVisitorWrapper(self)
    }

    fn on_implicit_param(&mut self, _ident: Ident, _kind: fhir::ParamKind, _node_id: NodeId) {}
    fn on_refine_param(&mut self, _param: &surface::RefineParam) {}
    fn on_loc(&mut self, _loc: Ident, _node_id: NodeId) {}
    fn on_path(&mut self, _path: &surface::ExprPath) {}
    fn on_base_sort(&mut self, _sort: &surface::BaseSort) {}
}

pub(crate) struct ScopedVisitorWrapper<V>(V);

impl<V: ScopedVisitor> ScopedVisitorWrapper<V> {
    fn with_scope(&mut self, kind: RibKind, node_id: Option<NodeId>, f: impl FnOnce(&mut Self)) {
        self.0.enter_scope(kind, node_id);
        f(self);
        self.0.exit_scope();
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
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_trait_assoc_reft(this, assoc_reft);
        });
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &surface::ImplAssocReft) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_impl_assoc_reft(this, assoc_reft);
        });
    }

    fn visit_qualifier(&mut self, qualifier: &surface::Qualifier) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_qualifier(this, qualifier);
        });
    }

    fn visit_defn(&mut self, defn: &surface::SpecFunc) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_defn(this, defn);
        });
    }

    fn visit_primop_prop(&mut self, prop: &surface::PrimOpProp) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_primop_prop(this, prop);
        });
    }

    fn visit_refine_param(&mut self, param: &surface::RefineParam) {
        self.on_refine_param(param);
        surface::visit::walk_refine_param(self, param);
    }

    fn visit_ty_alias(&mut self, ty_alias: &surface::TyAlias) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_ty_alias(this, ty_alias);
        });
    }

    fn visit_struct_def(&mut self, struct_def: &surface::StructDef) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_struct_def(this, struct_def);
        });
    }

    fn visit_enum_def(&mut self, enum_def: &surface::EnumDef) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_enum_def(this, enum_def);
        });
    }

    fn visit_variant(&mut self, variant: &surface::VariantDef) {
        self.with_scope(RibKind::Variant, Some(variant.node_id), |this| {
            surface::visit::walk_variant(this, variant);
        });
    }

    fn visit_trait_ref(&mut self, trait_ref: &surface::TraitRef) {
        match trait_ref.as_fn_trait_ref() {
            Some((in_arg, out_arg)) => {
                self.with_scope(RibKind::FnTraitInput, Some(trait_ref.node_id), |this| {
                    surface::visit::walk_generic_arg(this, in_arg);
                    this.with_scope(RibKind::Misc, None, |this| {
                        surface::visit::walk_generic_arg(this, out_arg);
                    });
                });
            }
            None => {
                self.with_scope(RibKind::Misc, None, |this| {
                    surface::visit::walk_trait_ref(this, trait_ref);
                });
            }
        }
    }

    fn visit_variant_ret(&mut self, ret: &surface::VariantRet) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_variant_ret(this, ret);
        });
    }

    fn visit_generics(&mut self, generics: &surface::Generics) {
        self.with_scope(RibKind::Misc, None, |this| {
            surface::visit::walk_generics(this, generics);
        });
    }

    fn visit_fn_sig(&mut self, fn_sig: &surface::FnSig) {
        self.with_scope(RibKind::FnInput, Some(fn_sig.node_id), |this| {
            surface::visit::walk_fn_sig(this, fn_sig);
        });
    }

    fn visit_fn_output(&mut self, output: &surface::FnOutput) {
        self.with_scope(RibKind::FnOutput, Some(output.node_id), |this| {
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
                self.with_scope(RibKind::Misc, None, |this| {
                    surface::visit::walk_refine_arg(this, arg);
                });
            }
            surface::RefineArg::Expr(expr) => self.visit_expr(expr),
        }
    }

    fn visit_path(&mut self, path: &surface::Path) {
        for arg in &path.refine {
            self.with_scope(RibKind::Misc, None, |this| this.visit_refine_arg(arg));
        }
        walk_list!(self, visit_path_segment, &path.segments);
    }

    fn visit_path_segment(&mut self, segment: &surface::PathSegment) {
        let is_box = self.is_box(segment);
        for (i, arg) in segment.args.iter().enumerate() {
            if is_box && i == 0 {
                self.visit_generic_arg(arg);
            } else {
                self.with_scope(RibKind::Misc, None, |this| this.visit_generic_arg(arg));
            }
        }
    }

    fn visit_ty(&mut self, ty: &surface::Ty) {
        let node_id = ty.node_id;
        match &ty.kind {
            surface::TyKind::Exists { bind, .. } => {
                self.with_scope(RibKind::Misc, None, |this| {
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
                self.with_scope(RibKind::Misc, None, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            surface::TyKind::BareFn(bare_fn) => {
                self.with_scope(RibKind::FnPtrInput, Some(bare_fn.node_id), |this| {
                    walk_list!(this, visit_ty, &bare_fn.inputs);
                    this.with_scope(RibKind::Misc, None, |this| {
                        this.visit_fn_ret_ty(&bare_fn.output);
                    });
                });
            }
            surface::TyKind::Array(..) => {
                self.with_scope(RibKind::Misc, None, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            _ => surface::visit::walk_ty(self, ty),
        }
    }

    fn visit_bty(&mut self, bty: &surface::BaseTy) {
        match &bty.kind {
            surface::BaseTyKind::Slice(_) | surface::BaseTyKind::Ptr(..) => {
                self.with_scope(RibKind::Misc, None, |this| {
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

type Binders = UnordMap<NodeId, Vec<(Ident, fhir::ParamKind, NodeId)>>;

/// Collects the implicit params bound in each binder scope (see [`ScopedVisitor::enter_scope`]),
/// reporting binders used in a position where they are not allowed. Implicit params must be
/// collected before resolving because they can be used before they are bound in the same scope,
/// e.g., `fn(x: i32{v: v > n}, n: i32)`.
struct BinderCollector<'a, 'genv, 'tcx> {
    resolver: &'a CrateResolver<'genv, 'tcx>,
    scopes: Vec<(RibKind, Option<NodeId>)>,
    binders: Binders,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> BinderCollector<'a, 'genv, 'tcx> {
    fn run(
        resolver: &'a CrateResolver<'genv, 'tcx>,
        f: impl FnOnce(&mut ScopedVisitorWrapper<Self>),
    ) -> Result<Binders> {
        let errors = Errors::new(resolver.genv.sess());
        let mut vis = Self { resolver, scopes: vec![], binders: Default::default(), errors }.wrap();
        f(&mut vis);
        vis.0.errors.to_result()?;
        Ok(vis.0.binders)
    }
}

impl ScopedVisitor for BinderCollector<'_, '_, '_> {
    fn is_box(&self, segment: &surface::PathSegment) -> bool {
        self.resolver
            .output
            .path_res_map
            .get(&segment.node_id)
            .map(|r| r.is_box(self.resolver.genv.tcx()))
            .unwrap_or(false)
    }

    fn enter_scope(&mut self, kind: RibKind, node_id: Option<NodeId>) {
        self.scopes.push((kind, node_id));
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn on_implicit_param(&mut self, ident: Ident, param_kind: fhir::ParamKind, param_id: NodeId) {
        let Some(&(rib_kind, node_id)) = self.scopes.last() else { return };
        let bind_kind = match param_kind {
            fhir::ParamKind::At => Some(surface::BindKind::At),
            fhir::ParamKind::Pound => Some(surface::BindKind::Pound),
            _ => None,
        };
        if let Some(bind_kind) = bind_kind
            && !rib_kind.allows_binder(bind_kind)
        {
            self.errors
                .emit(errors::IllegalBinder::new(ident.span, bind_kind));
            return;
        }
        if let Some(node_id) = node_id {
            self.binders
                .entry(node_id)
                .or_default()
                .push((ident, param_kind, param_id));
        }
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
    /// Parameters referenced in some expression. Used to skip unused
    /// [`fhir::ParamKind::Colon`]
    used_params: UnordSet<NodeId>,
    /// Implicit params to define when entering each binder scope.
    binders: Binders,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
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
            FluxItem::Use(_) => {
                // Use paths are resolved `CrateResolver::resolve_use_path`
                return Ok(());
            }
        };
        Self::new(resolver, Default::default()).run(sort_vars, |r| r.visit_flux_item(item))
    }

    pub(crate) fn resolve_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &surface::Item,
    ) -> Result {
        let binders = BinderCollector::run(resolver, |vis| vis.visit_item(item))?;
        Self::new(resolver, binders).run(&[], |vis| vis.visit_item(item))
    }

    pub(crate) fn resolve_trait_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &surface::TraitItemFn,
    ) -> Result {
        let binders = BinderCollector::run(resolver, |vis| vis.visit_trait_item(item))?;
        Self::new(resolver, binders).run(&[], |vis| vis.visit_trait_item(item))
    }

    pub(crate) fn resolve_impl_item(
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        item: &surface::ImplItemFn,
    ) -> Result {
        let binders = BinderCollector::run(resolver, |vis| vis.visit_impl_item(item))?;
        Self::new(resolver, binders).run(&[], |vis| vis.visit_impl_item(item))
    }

    fn new(resolver: &'a mut CrateResolver<'genv, 'tcx>, binders: Binders) -> Self {
        let errors = Errors::new(resolver.genv.sess());
        Self {
            resolver,
            param_defs: Default::default(),
            used_params: Default::default(),
            binders,
            errors,
        }
    }

    fn run(self, sort_vars: &[Ident], f: impl FnOnce(&mut ScopedVisitorWrapper<Self>)) -> Result {
        // Sort variables share the type namespace with sorts/types (see [`fhir::Namespace`]).
        self.resolver.push_rib(TypeNS, RibKind::Misc);
        for (idx, ident) in sort_vars.iter().enumerate() {
            self.resolver.define_res_in(
                Res::SortParam(idx),
                TypeNS,
                BindingSource::Explicit(*ident),
            );
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

        self.resolver.define_res_in(
            Res::Param(kind, param_id),
            ReftNS,
            BindingSource::Explicit(ident),
        );
    }

    fn emit_resolve_err(&mut self, err: ResolveError) {
        err.emit(&self.errors);
    }

    fn resolve_path(&mut self, path: &surface::ExprPath) {
        match self.try_resolve_expr_with_ribs(&path.segments) {
            Ok(res) => self.record_expr_res(path.node_id, res, path.segments.last().unwrap().ident),
            Err(ResolveError::NotFound) => self.emit_unresolved_expr_path(path),
            Err(err) => self.emit_resolve_err(err),
        }
    }

    fn resolve_ident(&mut self, ident: Ident, node_id: NodeId) {
        match self.try_resolve_expr_with_ribs(&[ident]) {
            Ok(res) => self.record_expr_res(node_id, res, ident),
            Err(ResolveError::NotFound) => self.emit_unresolved_ident(ident),
            Err(err) => self.emit_resolve_err(err),
        }
    }

    fn record_expr_res(&mut self, node_id: NodeId, res: PartialRes<NodeId>, ident: Ident) {
        // A param that cannot be refined, e.g., `fn(x: &mut i32) -> i32[x]`
        if let Some(Res::Param(fhir::ParamKind::Error, _)) = res.full_res() {
            self.errors.emit(errors::InvalidUnrefinedParam::new(ident));
        }
        if let Res::Param(_, param_id) = res.base_res() {
            self.used_params.insert(param_id);
        }
        self.resolver.output.path_res_map.insert(node_id, res);
    }

    fn try_resolve_expr_with_ribs<S: Segment>(
        &mut self,
        segments: &[S],
    ) -> std::result::Result<PartialRes<NodeId>, ResolveError> {
        // Try the refinement namespace first so that refinement params (and then flux funcs) take
        // precedence over Rust value/type bindings — in particular, a param shadows a Rust const of
        // the same name.
        //
        // An ambiguity in one namespace doesn't stop us from trying the next: a later namespace
        // may still resolve the name unambiguously, exactly as it would shadow it. But if nothing
        // resolves anywhere, we report the ambiguity rather than "unresolved name", which would
        // point the user at the wrong problem.
        let mut ambiguity = None;
        for ns in [ReftNS, ValueNS, TypeNS] {
            match self.resolver.resolve_path_with_ribs(segments, ns) {
                Ok(partial_res) => return Ok(partial_res),
                Err(ResolveError::Ambiguous(amb)) => ambiguity = ambiguity.or(Some(amb)),
                Err(ResolveError::NotFound) => {}
                Err(err @ ResolveError::OuterGeneric(_)) => return Err(err),
            }
        }
        Err(ambiguity.map_or(ResolveError::NotFound, ResolveError::Ambiguous))
    }

    fn resolve_sort_path(&mut self, path: &surface::SortPath) {
        // Sorts resolve in the type namespace: primitive/user sorts and sort parameters live there
        // alongside types, and any type can also denote a sort. We only report a *name* that fails
        // to resolve here; whether the resolved item is admissible as a sort (and the corresponding
        // diagnostic) is decided later in `conv_sort_path`.
        let res = match self.resolver.resolve_path_with_ribs(&path.segments, TypeNS) {
            Ok(res) => res,
            Err(ResolveError::NotFound) => {
                self.emit_unresolved_sort_path(path);
                PartialRes::new(fhir::Res::Err)
            }
            Err(err) => {
                self.emit_resolve_err(err);
                PartialRes::new(fhir::Res::Err)
            }
        };
        self.resolver.output.path_res_map.insert(path.node_id, res);
    }

    pub(crate) fn finish(self) -> Result {
        debug_assert!(self.binders.is_empty(), "binder scope not visited during resolution");
        let param_id_gen = IndexGen::new();
        let output = &mut self.resolver.output;
        for (node_id, def) in self.param_defs {
            match def.kind {
                fhir::ParamKind::Colon if !self.used_params.contains(&node_id) => continue,
                fhir::ParamKind::Error => continue,
                _ => {}
            }
            output
                .param_res_map
                .insert(node_id, (param_id_gen.fresh(), def.kind));
            if let Some(scope) = def.scope {
                output
                    .implicit_params
                    .entry(scope)
                    .or_default()
                    .push((def.ident, node_id));
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
            name: Segment::format_iter(&path.segments),
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
            name: Segment::format_iter(&path.segments),
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

    fn enter_scope(&mut self, kind: RibKind, node_id: Option<NodeId>) {
        self.resolver.push_rib(ReftNS, kind);
        if let Some(node_id) = node_id {
            for (ident, param_kind, param_id) in self.binders.remove(&node_id).unwrap_or_default() {
                self.define_param(ident, param_kind, param_id, Some(node_id));
            }
        }
    }

    fn exit_scope(&mut self) {
        self.resolver.pop_rib(ReftNS);
    }

    fn on_refine_param(&mut self, param: &surface::RefineParam) {
        self.define_param(
            param.ident,
            fhir::ParamKind::Explicit(param.mode.map(Into::into)),
            param.node_id,
            None,
        );
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
            surface::BaseSort::BitVec(_)
            | surface::BaseSort::SortOf(..)
            | surface::BaseSort::Tuple(_) => {}
        }
    }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use rustc_span::{Span, symbol::Ident};

    #[derive(Diagnostic)]
    #[diag("invalid use of refinement parameter", code = E0999)]
    pub(super) struct InvalidUnrefinedParam {
        #[primary_span]
        #[label("parameter `{$var}` refers to a type with no indices")]
        span: Span,
        var: Ident,
    }

    impl InvalidUnrefinedParam {
        pub(super) fn new(var: Ident) -> Self {
            Self { var, span: var.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag("illegal binder", code = E0999)]
    pub(super) struct IllegalBinder {
        #[primary_span]
        #[label("`{$kind}` binder not allowed in this position")]
        span: Span,
        kind: &'static str,
    }

    impl IllegalBinder {
        pub(super) fn new(span: Span, kind: surface::BindKind) -> Self {
            Self { span, kind: kind.token_str() }
        }
    }
}
