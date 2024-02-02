use std::ops::ControlFlow;

use flux_common::index::IndexGen;
use flux_middle::{fhir, FuncRes, LocRes, PathRes, ResolverOutput};
use flux_syntax::surface::{
    self,
    visit::{walk_ty, Visitor as _},
    Ident, NodeId,
};
use rustc_data_structures::{
    fx::{FxIndexMap, IndexEntry},
    unord::UnordMap,
};
use rustc_hash::FxHashMap;
use rustc_hir::{def::DefKind, OwnerId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, sym, symbol::kw, Symbol};

use super::CrateResolver;
use crate::sort_resolver::SelfRes;

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
struct ParamRes(ParamKind, NodeId);

impl ParamRes {
    fn node_id(self) -> NodeId {
        self.1
    }

    fn is_syntax_err(&self) -> bool {
        matches!(self, ParamRes(ParamKind::SyntaxError, _))
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ParamKind {
    Explicit,
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

impl ParamKind {
    fn is_allowed_in(self, kind: ScopeKind) -> bool {
        match self {
            ParamKind::At => {
                matches!(kind, ScopeKind::FnInput | ScopeKind::Variant)
            }
            ParamKind::Colon | ParamKind::Loc(_) => {
                matches!(kind, ScopeKind::FnInput)
            }
            ParamKind::Pound => matches!(kind, ScopeKind::FnOutput),
            ParamKind::SyntaxError => matches!(kind, ScopeKind::FnInput | ScopeKind::FnOutput),
            ParamKind::Explicit => todo!(),
        }
    }
}

impl From<surface::BindKind> for ParamKind {
    fn from(kind: surface::BindKind) -> Self {
        match kind {
            surface::BindKind::At => ParamKind::At,
            surface::BindKind::Pound => ParamKind::Pound,
        }
    }
}

pub(crate) trait ScopedVisitor: Sized {
    fn is_box(&self, path: &surface::Path) -> bool;
    fn enter_scope(&mut self, kind: ScopeKind) -> ControlFlow<()>;
    fn exit_scope(&mut self) {}

    fn wrap(self) -> ScopedVisitorWrapper<Self> {
        ScopedVisitorWrapper(self)
    }

    fn on_implicit_param(&mut self, _ident: Ident, _kind: ParamKind, _node_id: NodeId) {}
    fn on_generic_param(&mut self, _param: &surface::GenericParam) {}
    fn on_refine_param(&mut self, _name: Ident, _node_id: NodeId) {}
    fn on_enum_variant(&mut self, _variant: &surface::VariantDef) {}
    fn on_fn_sig(&mut self, _fn_sig: &surface::FnSig) {}
    fn on_fn_output(&mut self, _output: &surface::FnOutput) {}
    fn on_loc(&mut self, _loc: Ident, _node_id: NodeId) {}
    fn on_func(&mut self, _func: Ident, _node_id: NodeId) {}
    fn on_path(&mut self, _path: &surface::QPathExpr) {}
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

impl<'genv> RefinementResolver<'_, 'genv, '_> {
    pub(crate) fn run(self, f: impl FnOnce(&mut ScopedVisitorWrapper<Self>)) {
        let mut wrapper = self.wrap();
        f(&mut wrapper);
        wrapper.0.finish();
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
    fn visit_qualifier(&mut self, qualifier: &surface::Qualifier) {
        self.with_scope(ScopeKind::Misc, |this| {
            surface::visit::walk_qualifier(this, qualifier);
        });
    }

    fn visit_defn(&mut self, defn: &surface::FuncDef) {
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
                self.on_implicit_param(*bind, ParamKind::Colon, *node_id);
            }
            surface::Arg::StrgRef(loc, _, node_id) => {
                self.on_implicit_param(*loc, ParamKind::Loc(idx), *node_id);
            }
            surface::Arg::Ty(bind, ty, node_id) => {
                if let &Some(bind) = bind {
                    let param_kind = if let surface::TyKind::Base(bty) = &ty.kind {
                        if bty.is_hole() {
                            ParamKind::SyntaxError
                        } else {
                            ParamKind::Colon
                        }
                    } else {
                        ParamKind::SyntaxError
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
                self.on_implicit_param(*ident, ParamKind::from(*kind), *node_id);
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

        let is_box = self.is_box(path);
        for (i, arg) in path.generics.iter().enumerate() {
            if is_box && i == 0 {
                self.visit_generic_arg(arg);
            } else {
                self.with_scope(ScopeKind::Misc, |this| {
                    this.visit_generic_arg(arg);
                });
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
    params: Vec<(Ident, ParamKind, NodeId)>,
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
    ) -> Vec<(Ident, ParamKind, NodeId)> {
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

    fn on_implicit_param(&mut self, ident: Ident, param: ParamKind, node_id: NodeId) {
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

struct ParamDef {
    ident: Ident,
    param_id: NodeId,
    kind: ParamKind,
    scope: Option<NodeId>,
}

enum SortRes {
    Var(usize),
    Param(DefId),
    /// A `Self` parameter in a trait definition.
    SelfParam {
        trait_id: DefId,
    },
    /// An alias to another sort, e.g., when used inside an impl block
    SelfAlias {
        alias_to: DefId,
    },
}

fn self_res(tcx: TyCtxt, owner: OwnerId) -> Option<SortRes> {
    let def_id = owner.def_id.to_def_id();
    let mut opt_def_id = Some(def_id);
    while let Some(def_id) = opt_def_id {
        match tcx.def_kind(def_id) {
            DefKind::Trait => return Some(SortRes::SelfParam { trait_id: def_id }),
            DefKind::Impl { .. } => return Some(SortRes::SelfAlias { alias_to: def_id }),
            _ => {
                opt_def_id = tcx.opt_parent(def_id);
            }
        }
    }
    None
}

pub(crate) struct RefinementResolver<'a, 'genv, 'tcx> {
    tcx: TyCtxt<'tcx>,
    scopes: Vec<Scope>,
    sorts_res: UnordMap<Symbol, SortRes>,
    param_defs: Vec<ParamDef>,
    resolver: &'a mut CrateResolver<'genv, 'tcx>,
    func_res_map: FxHashMap<NodeId, FuncRes<NodeId>>,
    loc_res_map: FxHashMap<NodeId, LocRes<NodeId>>,
    path_res_map: FxHashMap<NodeId, PathRes<NodeId>>,
}

impl<'a, 'genv, 'tcx> RefinementResolver<'a, 'genv, 'tcx> {
    pub(crate) fn with_sort_params(
        tcx: TyCtxt<'tcx>,
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        sort_params: &[Symbol],
    ) -> Self {
        let sort_res = sort_params
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, SortRes::Var(i)))
            .collect();
        Self::new(tcx, resolver, sort_res)
    }

    pub(crate) fn with_generics(
        tcx: TyCtxt<'tcx>,
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        owner: OwnerId,
    ) -> Self {
        let generics = tcx.generics_of(owner);
        let mut sort_res: UnordMap<_, _> = generics
            .params
            .iter()
            .map(|p| (p.name, SortRes::Param(p.def_id)))
            .collect();
        if let Some(self_res) = self_res(tcx, owner) {
            sort_res.insert(kw::SelfUpper, self_res);
        }
        Self::new(tcx, resolver, sort_res)
    }

    fn new(
        tcx: TyCtxt<'tcx>,
        resolver: &'a mut CrateResolver<'genv, 'tcx>,
        sort_res: UnordMap<Symbol, SortRes>,
    ) -> Self {
        Self {
            tcx,
            resolver,
            sorts_res: sort_res,
            param_defs: Default::default(),
            scopes: Default::default(),
            func_res_map: Default::default(),
            loc_res_map: Default::default(),
            path_res_map: Default::default(),
        }
    }

    fn define_param(
        &mut self,
        ident: Ident,
        kind: ParamKind,
        param_id: NodeId,
        scope: Option<NodeId>,
    ) {
        self.param_defs
            .push(ParamDef { ident, param_id, kind, scope });

        let scope = self.scopes.last_mut().unwrap();
        match scope.bindings.entry(ident) {
            IndexEntry::Occupied(_) => todo!(),
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

    fn resolve_base_sort_ident(&mut self, ident: Ident, node_id: NodeId) {
        let sort = if ident.name == SORTS.int {
            fhir::Sort::Int
        } else if ident.name == sym::bool {
            fhir::Sort::Bool
        } else if ident.name == SORTS.real {
            fhir::Sort::Real
        } else if let Some(res) = self.sorts_res.get(&ident.name) {
            match *res {
                SortRes::Var(idx) => fhir::Sort::Var(idx),
                SortRes::Param(def_id) => fhir::Sort::Param(def_id),
                SortRes::SelfParam { trait_id } => fhir::Sort::SelfParam { trait_id },
                SortRes::SelfAlias { alias_to } => fhir::Sort::SelfAlias { alias_to },
            }
        } else if self.resolver.output.sort_decls.get(&ident.name).is_some() {
            let ctor = fhir::SortCtor::User { name: ident.name };
            fhir::Sort::App(ctor, &[])
        } else {
            todo!()
            // Err(self
            //     .genv
            //     .sess()
            //     .emit_err(errors::UnresolvedSort::new(*ident)))
        };
        self.resolver
            .output
            .refinements
            .sort_res_map
            .insert(node_id, sort);
    }

    fn resolve_sort_ctor(&mut self, ctor: Ident, node_id: NodeId) {
        let ctor = if ctor.name == SORTS.set {
            fhir::SortCtor::Set
        } else if ctor.name == SORTS.map {
            fhir::SortCtor::Map
        } else {
            todo!()
            // Err(self
            //     .genv
            //     .sess()
            //     .emit_err(errors::UnresolvedSort::new(ident)))
        };
        self.resolver
            .output
            .refinements
            .sort_ctor_res_map
            .insert(node_id, ctor);
    }

    pub(crate) fn finish(self) {
        let name_gen: IndexGen<fhir::Name> = IndexGen::new();
        let mut params = FxIndexMap::default();
        let mut name_for_param =
            |param_id| *params.entry(param_id).or_insert_with(|| name_gen.fresh());

        for (node_id, res) in self.func_res_map {
            let res = match res {
                FuncRes::Param(param_id) => FuncRes::Param(name_for_param(param_id)),
                FuncRes::Global(kind) => FuncRes::Global(kind),
            };
            self.resolver
                .output
                .refinements
                .func_res_map
                .insert(node_id, res);
        }

        for (node_id, LocRes(param_id, idx)) in self.loc_res_map {
            self.resolver
                .output
                .refinements
                .loc_res_map
                .insert(node_id, LocRes(name_for_param(param_id), idx));
        }

        for (node_id, res) in self.path_res_map {
            let res = match res {
                PathRes::Param(param_id) => PathRes::Param(name_for_param(param_id)),
                PathRes::Const(def_id) => PathRes::Const(def_id),
                PathRes::NumConst(val) => PathRes::NumConst(val),
            };
            self.resolver
                .output
                .refinements
                .path_res_map
                .insert(node_id, res);
        }

        for param_def in self.param_defs {
            let name = params.get(&param_def.param_id).copied();
            let (kind, name) = match param_def.kind {
                ParamKind::Explicit => {
                    let name = name.unwrap_or_else(|| name_gen.fresh());
                    (fhir::ParamKind::Explicit, name)
                }
                ParamKind::At => {
                    let name = name.unwrap_or_else(|| name_gen.fresh());
                    (fhir::ParamKind::At, name)
                }
                ParamKind::Pound => {
                    let name = name.unwrap_or_else(|| name_gen.fresh());
                    (fhir::ParamKind::Pound, name)
                }
                ParamKind::Colon => {
                    if let Some(name) = name {
                        (fhir::ParamKind::Colon, name)
                    } else {
                        continue;
                    }
                }
                ParamKind::Loc(idx) => {
                    let name = name.unwrap_or_else(|| name_gen.fresh());
                    (fhir::ParamKind::Loc(idx), name)
                }
                ParamKind::SyntaxError => continue,
            };
            let output = &mut self.resolver.output.refinements;
            output
                .param_res_map
                .insert(param_def.param_id, (name, kind));
            if let Some(scope) = param_def.scope {
                output
                    .implicit_params
                    .entry(scope)
                    .or_default()
                    .push((param_def.ident, param_def.param_id));
            }
        }
    }

    fn path_res_map(&self) -> &UnordMap<NodeId, fhir::Res> {
        &self.resolver_output().path_res_map
    }

    fn resolver_output(&self) -> &ResolverOutput {
        &self.resolver.output
    }
}

impl<'genv> ScopedVisitor for RefinementResolver<'_, 'genv, '_> {
    fn is_box(&self, path: &surface::Path) -> bool {
        let res = self.path_res_map()[&path.node_id];
        res.is_box(self.tcx)
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
            self.tcx,
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
            self.tcx,
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
            self.tcx,
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
        self.define_param(param.name, ParamKind::Explicit, param.node_id, None);
    }

    fn on_refine_param(&mut self, name: Ident, node_id: NodeId) {
        self.define_param(name, ParamKind::Explicit, node_id, None);
    }

    fn on_func(&mut self, func: Ident, node_id: NodeId) {
        if let Some(res) = self.find(func) {
            if res.is_syntax_err() {
                todo!();
            }
            self.func_res_map
                .insert(node_id, FuncRes::Param(res.node_id()));
            return;
        }
        if let Some(decl) = self.resolver_output().func_decls.get(&func.name) {
            self.func_res_map.insert(node_id, FuncRes::Global(*decl));
            return;
        }
        todo!("report error")
    }

    fn on_loc(&mut self, loc: Ident, node_id: NodeId) {
        match self.find(loc) {
            Some(res) => {
                match res {
                    ParamRes(ParamKind::Loc(idx), _) => {
                        self.loc_res_map.insert(node_id, LocRes(res.node_id(), idx));
                    }
                    _ => {
                        todo!()
                    }
                }
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
                if let Some(res) = self.find(*var) {
                    if res.is_syntax_err() {
                        todo!("report error");
                    }
                    self.path_res_map
                        .insert(path.node_id, PathRes::Param(res.node_id()));
                    return;
                }
                if let Some(const_def_id) = self.resolver_output().consts.get(&var.name) {
                    self.path_res_map
                        .insert(path.node_id, PathRes::Const(*const_def_id));
                    return;
                }
                todo!("report error {path:?}")
            }
            [typ, name] => {
                if let Some(res) = resolve_num_const(*typ, *name) {
                    self.resolver
                        .output
                        .refinements
                        .path_res_map
                        .insert(path.node_id, res);
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

    fn on_base_sort(&mut self, sort: &surface::BaseSort) {
        match sort {
            surface::BaseSort::Ident(ident, node_id) => {
                self.resolve_base_sort_ident(*ident, *node_id);
            }
            surface::BaseSort::App(ctor, _, node_id) => {
                self.resolve_sort_ctor(*ctor, *node_id);
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
    int: Symbol,
    real: Symbol,
    set: Symbol,
    map: Symbol,
}

pub(crate) static SORTS: std::sync::LazyLock<Sorts> = std::sync::LazyLock::new(|| {
    Sorts {
        int: Symbol::intern("int"),
        real: Symbol::intern("real"),
        set: Symbol::intern("Set"),
        map: Symbol::intern("Map"),
    }
});
