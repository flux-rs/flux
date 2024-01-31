use std::{collections::hash_map, ops::ControlFlow};

use flux_common::index::IndexGen;
use flux_middle::{fhir, ResolverOutput};
use flux_syntax::surface::{
    self,
    visit::{walk_ty, Visitor as _},
    Ident, NodeId,
};
use rustc_data_structures::{
    fx::{FxIndexMap, IndexEntry},
    unord::UnordMap,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, Span};

use crate::sort_resolver::SortResolver;

type ScopeId = surface::NodeId;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    FnInput,
    FnOutput,
    Variant,
    Misc,
}

impl ScopeKind {
    fn is_barrier(self) -> bool {
        matches!(self, ScopeKind::FnInput | ScopeKind::Variant)
    }

    fn is_binder_allowed(self, kind: surface::BindKind) -> bool {
        match self {
            ScopeKind::FnInput => matches!(kind, surface::BindKind::At),
            ScopeKind::FnOutput => matches!(kind, surface::BindKind::Pound),
            _ => false,
        }
    }
}

/// Parameters used during gathering.
#[derive(Debug, Clone, Copy)]
enum UnresolvedParam<'fhir> {
    /// A parameter declared in an explicit scope.
    Explicit(fhir::Sort<'fhir>),
    /// An implicitly scoped parameter.
    Implicit(ImplicitParam),
}

impl<'fhir> UnresolvedParam<'fhir> {
    fn is_syntax_err(&self) -> bool {
        matches!(self, UnresolvedParam::Implicit(ImplicitParam::SyntaxError))
    }
}

#[derive(Debug, Clone, Copy)]
enum ImplicitParam {
    /// A parameter declared with `@n` syntax.
    At,
    /// A parameter declared with `#n` syntax.
    Pound,
    /// A parameter declared with `x: T` syntax.
    Colon,
    /// A location declared with `x: &strg T` syntax.
    Loc(usize),
    /// A parameter that we know *syntactically* cannot be used inside a refinement. We track these
    /// parameters to report errors at the use site. For example, consider the following function:
    ///
    /// ```ignore
    /// fn(x: {v. i32[v] | v > 0}) -> i32[x]
    /// ```
    ///
    /// In this definition, we know syntatically that `x` binds to a non-base type so it's an error
    /// to use `x` as an index in the return type.
    SyntaxError,
}

impl ImplicitParam {
    fn is_allowed_in(self, kind: ScopeKind) -> bool {
        match self {
            ImplicitParam::At | ImplicitParam::Colon | ImplicitParam::Loc(_) => {
                matches!(kind, ScopeKind::FnInput)
            }
            ImplicitParam::Pound => matches!(kind, ScopeKind::FnOutput),
            ImplicitParam::SyntaxError => matches!(kind, ScopeKind::FnInput | ScopeKind::FnOutput),
        }
    }
}

impl From<surface::BindKind> for ImplicitParam {
    fn from(kind: surface::BindKind) -> Self {
        match kind {
            surface::BindKind::At => ImplicitParam::At,
            surface::BindKind::Pound => ImplicitParam::Pound,
        }
    }
}

trait ScopedVisitor: Sized {
    fn is_box(&self, path: &surface::Path) -> bool;
    fn enter_scope(&mut self, node_id: NodeId, kind: ScopeKind) -> ControlFlow<()>;
    fn exit_scope(&mut self) {}

    fn wrap(self) -> ScopedVisitorWrapper<Self> {
        ScopedVisitorWrapper(self)
    }

    fn on_implicit_param(&mut self, _ident: Ident, _kind: ImplicitParam) {}
    fn on_generic_param(&mut self, _param: &surface::GenericParam) {}
    fn on_refine_param(&mut self, _param: &surface::RefineParam) {}
    fn on_fn_sig(&mut self, _fn_sig: &surface::FnSig) {}
    fn on_fn_output(&mut self, _output: &surface::FnOutput) {}
    fn on_loc(&mut self, _loc: Ident, _node_id: NodeId) {}
    fn on_func(&mut self, _func: Ident, _node_id: NodeId) {}
    fn on_path(&mut self, _path: &surface::QPathExpr) {}
}

struct ScopedVisitorWrapper<V>(V);

impl<V: ScopedVisitor> ScopedVisitorWrapper<V> {
    fn with_scope(&mut self, node_id: NodeId, kind: ScopeKind, f: impl FnOnce(&mut Self)) {
        if let ControlFlow::Continue(_) = self.0.enter_scope(node_id, kind) {
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
    fn visit_generic_param(&mut self, param: &surface::GenericParam) {
        self.on_generic_param(param);
        surface::visit::walk_generic_param(self, param);
    }

    fn visit_refine_param(&mut self, param: &surface::RefineParam) {
        self.on_refine_param(param);
        surface::visit::walk_refine_param(self, param);
    }

    fn visit_ty_alias(&mut self, ty_alias: &surface::TyAlias) {
        self.with_scope(ty_alias.node_id, ScopeKind::Misc, |this| {
            surface::visit::walk_ty_alias(this, ty_alias);
        });
    }

    fn visit_struct_def(&mut self, struct_def: &surface::StructDef) {
        self.with_scope(struct_def.node_id, ScopeKind::Misc, |this| {
            surface::visit::walk_struct_def(this, struct_def);
        });
    }

    fn visit_enum_def(&mut self, enum_def: &surface::EnumDef) {
        self.with_scope(enum_def.node_id, ScopeKind::Misc, |this| {
            surface::visit::walk_enum_def(this, enum_def);
        });
    }

    fn visit_variant(&mut self, variant: &surface::VariantDef) {
        self.with_scope(variant.node_id, ScopeKind::Variant, |this| {
            surface::visit::walk_variant(this, variant);
        });
    }

    fn visit_fn_sig(&mut self, fn_sig: &surface::FnSig) {
        self.with_scope(fn_sig.node_id, ScopeKind::FnInput, |this| {
            this.on_fn_sig(fn_sig);
            surface::visit::walk_fn_sig(this, fn_sig);
        });
    }

    fn visit_fn_output(&mut self, output: &surface::FnOutput) {
        self.with_scope(output.node_id, ScopeKind::FnOutput, |this| {
            this.on_fn_output(output);
            surface::visit::walk_fn_output(this, output);
        });
    }

    fn visit_fun_arg(&mut self, arg: &surface::Arg, idx: usize) {
        match arg {
            surface::Arg::Constr(bind, _, _) => self.on_implicit_param(*bind, ImplicitParam::Colon),
            surface::Arg::StrgRef(loc, _, node_id) => {
                self.on_loc(*loc, *node_id);
                self.on_implicit_param(*loc, ImplicitParam::Loc(idx));
            }
            surface::Arg::Ty(bind, ty) => {
                if let &Some(bind) = bind {
                    if let surface::TyKind::Base(_) = &ty.kind {
                        self.on_implicit_param(bind, ImplicitParam::Colon);
                    } else {
                        self.on_implicit_param(bind, ImplicitParam::SyntaxError);
                    }
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
            surface::RefineArg::Bind(ident, kind, ..) => {
                self.on_implicit_param(*ident, ImplicitParam::from(*kind));
            }
            surface::RefineArg::Abs(_, body, node_id, _) => {
                self.with_scope(*node_id, ScopeKind::Misc, |this| {
                    surface::visit::walk_expr(this, body);
                });
            }
            surface::RefineArg::Expr(expr) => surface::visit::walk_expr(self, expr),
        }
    }

    fn visit_path(&mut self, path: &surface::Path) {
        // skip holes because they don't have a corresponding `Res`
        if path.is_hole() {
            return;
        }

        let is_box = self.is_box(path);
        for (i, arg) in path.generics.iter().enumerate() {
            if !is_box || i == 0 {
                self.with_scope(arg.node_id, ScopeKind::Misc, |this| {
                    surface::visit::walk_generic_arg(this, arg);
                });
            }
        }
    }

    fn visit_ty(&mut self, ty: &surface::Ty) {
        let node_id = ty.node_id;
        match &ty.kind {
            surface::TyKind::Exists { .. } => {
                self.with_scope(node_id, ScopeKind::Misc, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            surface::TyKind::GeneralExists { .. } => {
                self.with_scope(node_id, ScopeKind::Misc, |this| {
                    surface::visit::walk_ty(this, ty);
                });
            }
            _ => walk_ty(self, ty),
        }
    }

    fn visit_expr(&mut self, expr: &surface::Expr) {
        match &expr.kind {
            surface::ExprKind::QPath(path) => {
                self.on_path(path);
            }
            surface::ExprKind::App(func, _) => {
                self.on_func(*func, expr.node_id);
            }
            _ => {}
        }
        surface::visit::walk_expr(self, expr);
    }
}

struct ImplicitParamCollector<'a, 'tcx, F> {
    tcx: TyCtxt<'tcx>,
    path_res_map: &'a UnordMap<surface::NodeId, fhir::Res>,
    kind: ScopeKind,
    on_implicit_param: F,
}

impl<'a, 'tcx, F> ImplicitParamCollector<'a, 'tcx, F> {
    fn new(
        tcx: TyCtxt<'tcx>,
        path_res_map: &'a UnordMap<surface::NodeId, fhir::Res>,
        kind: ScopeKind,
        on_implicit_param: F,
    ) -> Self {
        Self { tcx, path_res_map, kind, on_implicit_param }
    }
}

impl<F> ScopedVisitor for ImplicitParamCollector<'_, '_, F>
where
    F: FnMut(Ident, ImplicitParam),
{
    fn is_box(&self, path: &surface::Path) -> bool {
        let res = self.path_res_map[&path.node_id];
        res.is_box(self.tcx)
    }

    fn enter_scope(&mut self, _: NodeId, kind: ScopeKind) -> ControlFlow<()> {
        if self.kind == kind {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }

    fn on_implicit_param(&mut self, ident: Ident, param: ImplicitParam) {
        (self.on_implicit_param)(ident, param);
    }
}

struct Scope<'genv> {
    kind: ScopeKind,
    bindings: FxIndexMap<Ident, UnresolvedParam<'genv>>,
}

impl<'genv> Scope<'genv> {
    fn new(kind: ScopeKind) -> Self {
        Self { kind, bindings: Default::default() }
    }
}

enum FuncRes {
    Param(fhir::Ident),
    Global(fhir::FuncKind),
}

struct LocRes {
    pub idx: usize,
    pub ident: fhir::Ident,
}

struct ExprResolver<'a, 'b, 'genv, 'tcx> {
    tcx: TyCtxt<'tcx>,
    scopes: UnordMap<ScopeId, Scope<'genv>>,
    scopes_stack: Vec<ScopeId>,
    name_gen: IndexGen<fhir::Name>,
    names: UnordMap<(ScopeId, Ident), fhir::Name>,
    sort_resolver: &'a SortResolver<'b, 'genv, 'tcx>,
    resolved_funcs: UnordMap<NodeId, FuncRes>,
    resolved_locs: UnordMap<NodeId, LocRes>,
    resolved_paths: UnordMap<NodeId, PathRes>,
}

struct ResolvedParam<'fhir> {
    name: fhir::Name,
    sort: fhir::Sort<'fhir>,
    kind: fhir::ParamKind,
    span: Span,
}

struct ExprResolverOutput<'fhir> {
    scopes: UnordMap<ScopeId, Vec<ResolvedParam<'fhir>>>,
    resolved_funcs: UnordMap<NodeId, FuncRes>,
    resolved_locs: UnordMap<NodeId, LocRes>,
    resolved_paths: UnordMap<NodeId, PathRes>,
}

impl<'a, 'b, 'genv, 'tcx> ExprResolver<'a, 'b, 'genv, 'tcx> {
    fn insert(&mut self, ident: Ident, param: UnresolvedParam<'genv>) {
        let scope = self.scopes_stack.last().unwrap();
        let bindings = &mut self.scopes.get_mut(scope).unwrap().bindings;
        match bindings.entry(ident) {
            IndexEntry::Occupied(_) => todo!(),
            IndexEntry::Vacant(entry) => {
                entry.insert(param);
            }
        }
    }

    fn find(&mut self, ident: Ident) -> Option<(ScopeId, UnresolvedParam)> {
        for scope_id in self.scopes_stack.iter().rev() {
            let scope = &self.scopes[scope_id];

            if scope.kind.is_barrier() {
                return None;
            }

            if let Some(param) = scope.bindings.get(&ident) {
                return Some((*scope_id, *param));
            }
        }
        None
    }

    fn fhir_ident(&mut self, scope: ScopeId, ident: Ident) -> fhir::Ident {
        let name = *self
            .names
            .entry((scope, ident))
            .or_insert_with(|| self.name_gen.fresh());
        fhir::Ident::new(name, ident)
    }

    fn into_output(self) -> ExprResolverOutput<'genv> {
        let scopes = self
            .scopes
            .into_items()
            .map(|(scope_id, scope)| {
                let bindings = scope
                    .bindings
                    .into_iter()
                    .filter_map(|(ident, param)| {
                        let name = self.names.get(&(scope_id, ident)).copied();
                        let (sort, kind) = match param {
                            UnresolvedParam::Explicit(sort) => (sort, fhir::ParamKind::Explicit),
                            UnresolvedParam::Implicit(ImplicitParam::At) => {
                                (fhir::Sort::Infer, fhir::ParamKind::At)
                            }
                            UnresolvedParam::Implicit(ImplicitParam::Pound) => {
                                (fhir::Sort::Infer, fhir::ParamKind::Pound)
                            }
                            UnresolvedParam::Implicit(ImplicitParam::Colon) => {
                                if name.is_some() {
                                    (fhir::Sort::Infer, fhir::ParamKind::Colon)
                                } else {
                                    return None;
                                }
                            }
                            UnresolvedParam::Implicit(ImplicitParam::Loc(idx)) => {
                                (fhir::Sort::Infer, fhir::ParamKind::Loc(idx))
                            }
                            UnresolvedParam::Implicit(ImplicitParam::SyntaxError) => return None,
                        };
                        let name = name.unwrap_or_else(|| self.name_gen.fresh());
                        Some(ResolvedParam { name, kind, sort, span: ident.span })
                    })
                    .collect();
                (scope_id, bindings)
            })
            .collect();
        ExprResolverOutput {
            scopes,
            resolved_funcs: self.resolved_funcs,
            resolved_locs: self.resolved_locs,
            resolved_paths: self.resolved_paths,
        }
    }

    fn path_res_map(&self) -> &'a UnordMap<NodeId, fhir::Res> {
        &self.resolver_output().path_res_map
    }

    fn resolver_output(&self) -> &'a ResolverOutput {
        self.sort_resolver.resolver_output
    }
}

impl<'genv> ScopedVisitor for ExprResolver<'_, '_, 'genv, '_> {
    fn is_box(&self, path: &surface::Path) -> bool {
        let res = self.path_res_map()[&path.node_id];
        res.is_box(self.tcx)
    }

    fn enter_scope(&mut self, scope_id: ScopeId, kind: ScopeKind) -> ControlFlow<()> {
        self.scopes.insert(scope_id, Scope::new(kind));
        self.scopes_stack.push(scope_id);
        ControlFlow::Continue(())
    }

    fn exit_scope(&mut self) {
        self.scopes_stack.pop();
    }

    fn on_fn_sig(&mut self, fn_sig: &surface::FnSig) {
        ImplicitParamCollector::new(
            self.tcx,
            self.path_res_map(),
            ScopeKind::FnInput,
            |ident, param| self.insert(ident, UnresolvedParam::Implicit(param)),
        )
        .wrap()
        .visit_fn_sig(fn_sig);
    }

    fn on_fn_output(&mut self, output: &surface::FnOutput) {
        ImplicitParamCollector::new(
            self.tcx,
            self.path_res_map(),
            ScopeKind::FnOutput,
            |ident, param| self.insert(ident, UnresolvedParam::Implicit(param)),
        )
        .wrap()
        .visit_fn_output(output);
    }

    fn on_generic_param(&mut self, param: &surface::GenericParam) {
        let surface::GenericParamKind::Refine { sort } = &param.kind else { return };
        match self.sort_resolver.resolve_sort(sort) {
            Ok(sort) => {
                self.insert(param.name, UnresolvedParam::Explicit(sort));
            }
            Err(_) => todo!(),
        }
    }

    fn on_refine_param(&mut self, param: &surface::RefineParam) {
        match self.sort_resolver.resolve_sort(&param.sort) {
            Ok(sort) => {
                self.insert(param.name, UnresolvedParam::Explicit(sort));
            }
            Err(_) => todo!(),
        }
    }

    fn on_func(&mut self, func: Ident, node_id: NodeId) {
        if let Some((scope, param)) = self.find(func) {
            if param.is_syntax_err() {
                todo!();
            }
            let func = self.fhir_ident(scope, func);
            self.resolved_funcs.insert(node_id, FuncRes::Param(func));
            return;
        }
        if let Some(decl) = self.resolver_output().func_decls.get(&func.name) {
            self.resolved_funcs.insert(node_id, FuncRes::Global(*decl));
            return;
        }
        todo!("report error")
    }

    fn on_loc(&mut self, loc: Ident, node_id: NodeId) {
        match self.find(loc) {
            Some((scope, UnresolvedParam::Implicit(ImplicitParam::Loc(idx)))) => {
                let loc = self.fhir_ident(scope, loc);
                self.resolved_locs
                    .insert(node_id, LocRes { idx, ident: loc });
            }
            Some((_, UnresolvedParam::Implicit(ImplicitParam::SyntaxError))) => {
                todo!()
            }
            Some(_) => {
                todo!()
            }
            None => {
                todo!()
                // Err(self.emit_err(errors::UnresolvedVar::from_ident(loc, "location")))
            }
        }
    }

    fn on_path(&mut self, path: &surface::QPathExpr) {
        match &path.segments[..] {
            [var] => {
                if let Some((scope, param)) = self.find(*var) {
                    if param.is_syntax_err() {
                        todo!("report error");
                    }
                    let var = self.fhir_ident(scope, *var);
                    self.resolved_paths
                        .insert(path.node_id, PathRes::Param(var));
                    return;
                }
                if let Some(const_def_id) = self.resolver_output().consts.get(&var.name) {
                    self.resolved_paths
                        .insert(path.node_id, PathRes::Const(*const_def_id));
                    return;
                }
                todo!("report error")
            }
            [typ, name] => {
                if let Some(res) = resolve_num_const(*typ, *name) {
                    self.resolved_paths.insert(path.node_id, res);
                    return;
                }
                todo!("report error")
            }
            _ => {
                todo!()
                // Err(self.emit_err(errors::UnresolvedVar::from_qpath(path, "type-3")))
            }
        }
    }
}

enum PathRes {
    Param(fhir::Ident),
    Const(DefId),
    NumConst(i128),
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
