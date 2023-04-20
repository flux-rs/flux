//! Conversion from types in [`fhir`] to types in [`rty`]
//!
//! Conversion assumes well-formedness and will panic if type are not well-formed. Among other things,
//! well-formedness implies:
//! 1. Names are bound correctly.
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted.
use std::borrow::Borrow;

use flux_common::{bug, span_bug};
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, FhirId, SurfaceIdent},
    global_env::GlobalEnv,
    intern::List,
    queries::QueryResult,
    rty::{self, fold::TypeFoldable, DebruijnIndex},
    rustc,
};
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    PrimTy,
};
use rustc_middle::ty::TyCtxt;

pub struct ConvCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    wfckresults: &'a fhir::WfckResults,
}

struct Env {
    layers: Vec<Layer>,
    early_bound: FxIndexMap<fhir::Name, (fhir::Sort, rty::Sort)>,
}

#[derive(Debug)]
enum Layer {
    List(FxIndexMap<fhir::Name, ListEntry>),
    Single(fhir::Name, fhir::Sort, rty::Sort),
}

#[derive(Debug)]
enum ListEntry {
    Sort {
        sort: fhir::Sort,
        infer_mode: rty::InferMode,
        conv: rty::Sort,
        /// The index of the entry in the layer skipping all [`ListEntry::Unit`].
        idx: u32,
    },
    /// We track parameters of unit sort separately because we avoid creating bound variables for them.
    Unit,
}

#[derive(Debug)]
struct LookupResult<'a> {
    name: fhir::Ident,
    kind: LookupResultKind<'a>,
}

#[derive(Debug)]
enum LookupResultKind<'a> {
    LateBoundList { level: u32, entry: &'a ListEntry },
    LateBoundSingle { level: u32, sort: &'a fhir::Sort, conv: &'a rty::Sort },
    EarlyBound { idx: u32, sort: &'a fhir::Sort, conv: &'a rty::Sort },
}

pub(crate) fn expand_type_alias(
    genv: &GlobalEnv,
    alias: &fhir::TyAlias,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let cx = ConvCtxt::new(genv, wfckresults);

    let mut env = Env::new(genv, &alias.early_bound_params);
    env.push_layer(Layer::list(&cx, &alias.index_params, false));

    let ty = cx.conv_ty(&mut env, &alias.ty)?;
    let sort = env.pop_layer().into_sort();
    Ok(rty::Binder::new(ty, sort))
}

pub(crate) fn conv_generics(
    rust_generics: &rustc::ty::Generics,
    generics: &fhir::Generics,
) -> rty::Generics {
    let mut fhir_params = generics.params.iter();
    let params = rust_generics
        .params
        .iter()
        .flat_map(|rust_param| {
            fhir_params
                .find(|param| rust_param.def_id == param.def_id.to_def_id())
                .map(|param| {
                    let kind = match &param.kind {
                        fhir::GenericParamDefKind::Type { default } => {
                            rty::GenericParamDefKind::Type { has_default: default.is_some() }
                        }
                        fhir::GenericParamDefKind::BaseTy => rty::GenericParamDefKind::BaseTy,
                        fhir::GenericParamDefKind::Lifetime => rty::GenericParamDefKind::Lifetime,
                    };
                    rty::GenericParamDef {
                        kind,
                        def_id: rust_param.def_id,
                        index: rust_param.index,
                        name: rust_param.name,
                    }
                })
        })
        .collect();
    rty::Generics {
        params,
        parent_count: rust_generics.orig.parent_count,
        parent: rust_generics.orig.parent,
    }
}

pub(crate) fn adt_def_for_struct(
    genv: &GlobalEnv,
    invariants: Vec<rty::Invariant>,
    struct_def: &fhir::StructDef,
) -> rty::AdtDef {
    let sort =
        rty::Sort::tuple(conv_sorts(genv.early_cx(), genv.index_sorts_of(struct_def.owner_id)));
    let adt_def = genv.tcx.adt_def(struct_def.owner_id);
    rty::AdtDef::new(adt_def, sort, invariants, struct_def.is_opaque())
}

pub(crate) fn adt_def_for_enum(
    genv: &GlobalEnv,
    invariants: Vec<rty::Invariant>,
    enum_def: &fhir::EnumDef,
) -> rty::AdtDef {
    let sort =
        rty::Sort::tuple(conv_sorts(genv.early_cx(), genv.index_sorts_of(enum_def.owner_id)));
    rty::AdtDef::new(genv.tcx.adt_def(enum_def.owner_id), sort, invariants, false)
}

pub(crate) fn conv_invariants(
    genv: &GlobalEnv,
    params: &[fhir::RefineParam],
    invariants: &[fhir::Expr],
    wfckresults: &fhir::WfckResults,
) -> Vec<rty::Invariant> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[]);
    env.push_layer(Layer::list(&cx, params, false));
    cx.conv_invariants(&env, invariants)
}

pub(crate) fn conv_defn(
    genv: &GlobalEnv,
    defn: &fhir::Defn,
    wfckresults: &fhir::WfckResults,
) -> rty::Defn {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[]);
    env.push_layer(Layer::list(&cx, &defn.args, false));
    let expr = cx.conv_expr(&env, &defn.expr);
    let expr = rty::Binder::new(expr, env.pop_layer().into_sort());
    rty::Defn { name: defn.name, expr }
}

pub fn conv_qualifier(
    genv: &GlobalEnv,
    qualifier: &fhir::Qualifier,
    wfckresults: &fhir::WfckResults,
) -> rty::Qualifier {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[]);
    env.push_layer(Layer::list(&cx, &qualifier.args, false));
    let body = cx.conv_expr(&env, &qualifier.expr);
    let body = rty::Binder::new(body, env.pop_layer().into_sort());
    rty::Qualifier { name: qualifier.name, body, global: qualifier.global }
}

pub(crate) fn conv_fn_sig(
    genv: &GlobalEnv,
    fn_sig: &fhir::FnSig,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::PolyFnSig> {
    let cx = ConvCtxt::new(genv, wfckresults);

    let mut env = Env::new(genv, &[]);
    env.push_layer(Layer::list(&cx, &fn_sig.params, true));

    let mut requires = vec![];
    for constr in &fn_sig.requires {
        requires.push(cx.conv_constr(&mut env, constr)?);
    }

    let mut args = vec![];
    for ty in &fn_sig.args {
        args.push(cx.conv_ty(&mut env, ty)?);
    }

    let output = cx.conv_fn_output(&mut env, &fn_sig.output)?;

    let params = env.pop_layer().into_fun_params();
    Ok(rty::PolyFnSig::new(params, rty::FnSig::new(requires, args, output)))
}

pub(crate) fn conv_ty(
    genv: &GlobalEnv,
    ty: &fhir::Ty,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let mut env = Env::new(genv, &[]);
    let ty = ConvCtxt::new(genv, wfckresults).conv_ty(&mut env, ty)?;
    Ok(rty::Binder::new(ty, rty::Sort::unit()))
}

impl<'a, 'tcx> ConvCtxt<'a, 'tcx> {
    fn new(genv: &'a GlobalEnv<'a, 'tcx>, wfckresults: &'a fhir::WfckResults) -> Self {
        Self { genv, wfckresults }
    }

    fn conv_fn_output(
        &self,
        env: &mut Env,
        output: &fhir::FnOutput,
    ) -> QueryResult<rty::Binder<rty::FnOutput>> {
        env.push_layer(Layer::list(self, &output.params, true));

        let ret = self.conv_ty(env, &output.ret)?;
        let ensures: List<rty::Constraint> = output
            .ensures
            .iter()
            .map(|constr| self.conv_constr(env, constr))
            .try_collect()?;
        let output = rty::FnOutput::new(ret, ensures);

        let sort = env.pop_layer().into_sort();

        Ok(rty::Binder::new(output, sort))
    }

    pub(crate) fn conv_enum_def_variants(
        genv: &GlobalEnv,
        enum_def: &fhir::EnumDef,
        wfckresults: &fhir::WfckResults,
    ) -> QueryResult<Vec<rty::PolyVariant>> {
        enum_def
            .variants
            .iter()
            .map(|variant_def| ConvCtxt::conv_enum_variant(genv, variant_def, wfckresults))
            .try_collect()
    }

    fn conv_enum_variant(
        genv: &GlobalEnv,
        variant: &fhir::VariantDef,
        wfckresults: &fhir::WfckResults,
    ) -> QueryResult<rty::PolyVariant> {
        let cx = ConvCtxt::new(genv, wfckresults);

        let mut env = Env::new(genv, &[]);
        env.push_layer(Layer::list(&cx, &variant.params, true));

        let fields = variant
            .fields
            .iter()
            .map(|ty| cx.conv_ty(&mut env, ty))
            .try_collect()?;
        let args = rty::Index::from(cx.conv_refine_arg(&mut env, &variant.ret.idx));
        let ret = cx.conv_base_ty(&mut env, &variant.ret.bty, args)?;
        let variant = rty::VariantDef::new(fields, ret);

        let sort = env.pop_layer().to_sort();
        Ok(rty::Binder::new(variant, sort))
    }

    pub(crate) fn conv_struct_def_variant(
        genv: &GlobalEnv,
        struct_def: &fhir::StructDef,
        wfckresults: &fhir::WfckResults,
    ) -> QueryResult<rty::Opaqueness<rty::PolyVariant>> {
        let cx = ConvCtxt::new(genv, wfckresults);
        let mut env = Env::new(genv, &[]);
        env.push_layer(Layer::list(&cx, &struct_def.params, false));

        let def_id = struct_def.owner_id.def_id;
        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let fields = fields
                .iter()
                .map(|field_def| cx.conv_ty(&mut env, &field_def.ty))
                .try_collect()?;

            let substs = genv
                .generics_of(def_id)?
                .params
                .iter()
                .map(|param| {
                    match param.kind {
                        rty::GenericParamDefKind::Type { .. } => {
                            let param_ty = rty::ParamTy { index: param.index, name: param.name };
                            rty::GenericArg::Ty(rty::Ty::param(param_ty))
                        }
                        rty::GenericParamDefKind::BaseTy => {
                            bug!("generic base type in struct definition not suported")
                        }
                        rty::GenericParamDefKind::Lifetime => rty::GenericArg::Lifetime,
                    }
                })
                .collect_vec();

            let sort = env.pop_layer().to_sort();
            let ret = rty::Ty::indexed(
                rty::BaseTy::adt(genv.adt_def(def_id)?, substs),
                rty::Expr::nu().eta_expand_tuple(&sort),
            );
            let variant = rty::VariantDef::new(fields, ret);
            Ok(rty::Opaqueness::Transparent(rty::Binder::new(variant, sort)))
        } else {
            Ok(rty::Opaqueness::Opaque)
        }
    }

    fn conv_constr(
        &self,
        env: &mut Env,
        constr: &fhir::Constraint,
    ) -> QueryResult<rty::Constraint> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                Ok(rty::Constraint::Type(env.lookup(*loc).to_path(), self.conv_ty(env, ty)?))
            }
            fhir::Constraint::Pred(pred) => Ok(rty::Constraint::Pred(self.conv_expr(env, pred))),
        }
    }

    fn conv_ty(&self, env: &mut Env, ty: &fhir::Ty) -> QueryResult<rty::Ty> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => {
                match self.genv.early_cx().sort_of_bty(bty) {
                    Some(sort) => {
                        let sort = conv_sort(self.early_cx(), &sort);

                        if sort.is_unit() {
                            let idx = rty::Index::from(rty::Expr::unit());
                            self.conv_base_ty(env, bty, idx)
                        } else {
                            env.push_layer(Layer::empty());
                            let idx = rty::Index::from(rty::Expr::nu());
                            let ty = self.conv_base_ty(env, bty, idx)?;
                            env.pop_layer();
                            Ok(rty::Ty::exists(rty::Binder::new(ty, sort)))
                        }
                    }
                    None => {
                        let def_id = bty.expect_param();
                        Ok(rty::Ty::param(def_id_to_param_ty(self.genv.tcx, def_id.expect_local())))
                    }
                }
            }
            fhir::TyKind::Indexed(bty, idx) => {
                let idxs = rty::Index::from(self.conv_refine_arg(env, idx));
                self.conv_base_ty(env, bty, idxs)
            }
            fhir::TyKind::Exists(params, ty) => {
                let layer = if let [param] = &params[..] {
                    Layer::single(self, param)
                } else {
                    Layer::list(self, params, false)
                };
                env.push_layer(layer);
                let ty = self.conv_ty(env, ty)?;
                let sort = env.pop_layer().into_sort();
                if sort.is_unit() {
                    Ok(ty.shift_out_escaping(1))
                } else {
                    Ok(rty::Ty::exists(rty::Binder::new(ty, sort)))
                }
            }
            fhir::TyKind::Ptr(loc) => {
                Ok(rty::Ty::ptr(rty::RefKind::Mut, env.lookup(*loc).to_path()))
            }
            fhir::TyKind::Ref(rk, ty) => {
                Ok(rty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(env, ty)?))
            }
            fhir::TyKind::Tuple(tys) => {
                let tys: List<rty::Ty> =
                    tys.iter().map(|ty| self.conv_ty(env, ty)).try_collect()?;
                Ok(rty::Ty::tuple(tys))
            }
            fhir::TyKind::Array(ty, len) => {
                Ok(rty::Ty::array(self.conv_ty(env, ty)?, rty::Const { val: len.val }))
            }
            fhir::TyKind::Never => Ok(rty::Ty::never()),
            fhir::TyKind::Constr(pred, ty) => {
                let pred = self.conv_expr(env, pred);
                Ok(rty::Ty::constr(pred, self.conv_ty(env, ty)?))
            }
            fhir::TyKind::RawPtr(ty, mutability) => {
                Ok(rty::Ty::indexed(
                    rty::BaseTy::RawPtr(self.conv_ty(env, ty)?, *mutability),
                    rty::Expr::unit(),
                ))
            }
        }
    }

    fn conv_refine_arg(
        &self,
        env: &mut Env,
        arg: &fhir::RefineArg,
    ) -> (rty::Expr, rty::TupleTree<bool>) {
        match arg {
            fhir::RefineArg::Expr { expr, is_binder, .. } => {
                (self.conv_expr(env, expr), rty::TupleTree::Leaf(*is_binder))
            }
            fhir::RefineArg::Abs(params, body, _, fhir_id) => {
                let layer = Layer::list(self, params, false);

                env.push_layer(layer);
                let pred = self.conv_expr(env, body);
                let sort = env.pop_layer().to_sort();

                let body = rty::Binder::new(pred, sort);
                let expr = self.add_coercions(rty::Expr::abs(body), *fhir_id);
                (expr, rty::TupleTree::Leaf(false))
            }
            fhir::RefineArg::Record(_, flds, ..) => {
                let mut exprs = vec![];
                let mut is_binder = vec![];
                for arg in flds {
                    let (e, i) = self.conv_refine_arg(env, arg);
                    exprs.push(e);
                    is_binder.push(i);
                }
                (rty::Expr::tuple(exprs), rty::TupleTree::Tuple(List::from_vec(is_binder)))
            }
        }
    }

    fn conv_ref_kind(rk: fhir::RefKind) -> rty::RefKind {
        match rk {
            fhir::RefKind::Mut => rty::RefKind::Mut,
            fhir::RefKind::Shr => rty::RefKind::Shr,
        }
    }

    fn conv_base_ty(
        &self,
        env: &mut Env,
        bty: &fhir::BaseTy,
        idx: rty::Index,
    ) -> QueryResult<rty::Ty> {
        match &bty.kind {
            fhir::BaseTyKind::Path(path) => self.conv_path(env, path, idx),
            fhir::BaseTyKind::Slice(ty) => {
                let slice = rty::BaseTy::slice(self.conv_ty(env, ty)?);
                Ok(rty::Ty::indexed(slice, idx))
            }
        }
    }

    fn conv_path(&self, env: &mut Env, path: &fhir::Path, idx: rty::Index) -> QueryResult<rty::Ty> {
        let bty = match &path.res {
            fhir::Res::PrimTy(PrimTy::Bool) => rty::BaseTy::Bool,
            fhir::Res::PrimTy(PrimTy::Str) => rty::BaseTy::Str,
            fhir::Res::PrimTy(PrimTy::Char) => rty::BaseTy::Char,
            fhir::Res::PrimTy(PrimTy::Int(int_ty)) => {
                rty::BaseTy::Int(rustc_middle::ty::int_ty(*int_ty))
            }
            fhir::Res::PrimTy(PrimTy::Uint(uint_ty)) => {
                rty::BaseTy::Uint(rustc_middle::ty::uint_ty(*uint_ty))
            }
            fhir::Res::PrimTy(PrimTy::Float(float_ty)) => {
                rty::BaseTy::Float(rustc_middle::ty::float_ty(*float_ty))
            }
            fhir::Res::Struct(did) | fhir::Res::Enum(did) => {
                let adt_def = self.genv.adt_def(*did)?;
                let substs = self.conv_generic_args(env, *did, &path.generics)?;
                rty::BaseTy::adt(adt_def, substs)
            }
            fhir::Res::Param(def_id) => {
                rty::BaseTy::Param(def_id_to_param_ty(self.genv.tcx, def_id.expect_local()))
            }
            fhir::Res::Alias(def_id) => {
                let generics = self.conv_generic_args(env, *def_id, &path.generics)?;
                let refine = path
                    .refine
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg).0)
                    .collect_vec();
                let index_sorts = conv_sorts(self.early_cx(), self.genv.index_sorts_of(*def_id));
                let idx = idx.expr.eta_expand_tuple(&rty::Sort::tuple(index_sorts));
                return Ok(self
                    .genv
                    .type_of(*def_id)?
                    .subst(&generics, &refine)
                    .replace_bvar(&idx));
            }
        };
        Ok(rty::Ty::indexed(bty, idx))
    }

    fn conv_generic_args(
        &self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::Ty],
    ) -> QueryResult<Vec<rty::GenericArg>> {
        let mut i = 0;
        self.genv
            .generics_of(def_id)?
            .params
            .iter()
            .map(|param| {
                match param.kind {
                    rty::GenericParamDefKind::Type { has_default } => {
                        if i < args.len() {
                            i += 1;
                            Ok(rty::GenericArg::Ty(self.conv_ty(env, &args[i - 1])?))
                        } else {
                            debug_assert!(has_default);
                            let ty = self
                                .genv
                                .type_of(param.def_id)?
                                .subst_generics(&[])
                                .replace_bvar(&rty::Expr::unit());
                            Ok(rty::GenericArg::Ty(ty))
                        }
                    }
                    rty::GenericParamDefKind::BaseTy => {
                        bug!("generic base type arguments not supported yet")
                    }
                    rty::GenericParamDefKind::Lifetime => Ok(rty::GenericArg::Lifetime),
                }
            })
            .try_collect()
    }

    fn early_cx(&self) -> &EarlyCtxt<'a, 'tcx> {
        self.genv.early_cx()
    }

    fn resolve_param_sort(&self, param: &fhir::RefineParam) -> fhir::Sort {
        if fhir::Sort::Wildcard == param.sort {
            self.node_sort(param.fhir_id).clone()
        } else {
            param.sort.clone()
        }
    }

    fn node_sort(&self, fhir_id: FhirId) -> &fhir::Sort {
        self.wfckresults.node_sorts().get(fhir_id).unwrap()
    }
}

impl Env {
    fn new(genv: &GlobalEnv, early_bound: &[fhir::RefineParam]) -> Self {
        let early_bound = early_bound
            .iter()
            .map(|param| {
                let conv = conv_sort(genv.early_cx(), &param.sort);
                (param.name(), (param.sort.clone(), conv))
            })
            .collect();
        Self { layers: vec![], early_bound }
    }

    fn push_layer(&mut self, layer: Layer) {
        self.layers.push(layer);
    }

    fn pop_layer(&mut self) -> Layer {
        self.layers.pop().expect("bottom of layer stack")
    }

    fn top_layer(&self) -> &Layer {
        self.layers.last().expect("bottom of layer stack")
    }

    fn lookup(&self, name: fhir::Ident) -> LookupResult {
        for (level, layer) in self.layers.iter().rev().enumerate() {
            if let Some(kind) = layer.get(name.name, level as u32) {
                return LookupResult { name, kind };
            }
        }
        if let Some((idx, _, (sort, conv))) = self.early_bound.get_full(&name.name) {
            LookupResult {
                name,
                kind: LookupResultKind::EarlyBound { idx: idx as u32, sort, conv },
            }
        } else {
            span_bug!(name.span(), "no entry found for key: `{:?}`", name);
        }
    }
}

impl ConvCtxt<'_, '_> {
    fn conv_expr(&self, env: &Env, expr: &fhir::Expr) -> rty::Expr {
        let fhir_id = expr.fhir_id;
        let expr = match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
            fhir::ExprKind::Var(var) => env.lookup(*var).to_expr(),
            fhir::ExprKind::Literal(lit) => rty::Expr::constant(conv_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                rty::Expr::binary_op(*op, self.conv_expr(env, e1), self.conv_expr(env, e2))
            }
            fhir::ExprKind::UnaryOp(op, e) => rty::Expr::unary_op(*op, self.conv_expr(env, e)),
            fhir::ExprKind::App(func, args) => {
                rty::Expr::app(
                    self.conv_func(env, func),
                    rty::Expr::tuple(self.conv_exprs(env, args)),
                )
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                rty::Expr::ite(
                    self.conv_expr(env, p),
                    self.conv_expr(env, e1),
                    self.conv_expr(env, e2),
                )
            }
            fhir::ExprKind::Dot(var, fld) => env.lookup(*var).get_field(self.genv.early_cx(), *fld),
        };
        self.add_coercions(expr, fhir_id)
    }

    fn conv_func(&self, env: &Env, func: &fhir::Func) -> rty::Expr {
        let expr = match func {
            fhir::Func::Var(ident, _) => env.lookup(*ident).to_expr(),
            fhir::Func::Global(sym, kind, ..) => rty::Expr::global_func(*sym, *kind),
        };
        self.add_coercions(expr, func.fhir_id())
    }

    fn conv_exprs(&self, env: &Env, exprs: &[fhir::Expr]) -> List<rty::Expr> {
        List::from_iter(exprs.iter().map(|e| self.conv_expr(env, e)))
    }

    fn conv_invariants(&self, env: &Env, invariants: &[fhir::Expr]) -> Vec<rty::Invariant> {
        invariants
            .iter()
            .map(|invariant| self.conv_invariant(env, invariant))
            .collect()
    }

    fn conv_invariant(&self, env: &Env, invariant: &fhir::Expr) -> rty::Invariant {
        rty::Invariant {
            pred: rty::Binder::new(self.conv_expr(env, invariant), env.top_layer().to_sort()),
        }
    }

    fn add_coercions(&self, mut expr: rty::Expr, fhir_id: FhirId) -> rty::Expr {
        if let Some(coercions) = self.wfckresults.coercions().get(fhir_id) {
            for coercion in coercions {
                expr = match coercion {
                    fhir::Coercion::Inject => rty::Expr::tuple(vec![expr]),
                    fhir::Coercion::Project => rty::Expr::tuple_proj(expr, 0),
                };
            }
        }
        expr
    }
}

impl Layer {
    fn list(cx: &ConvCtxt, params: &[fhir::RefineParam], filter_unit: bool) -> Self {
        let mut idx = 0;
        let map = params
            .iter()
            .map(|param| {
                let sort = cx.resolve_param_sort(param);
                let entry = ListEntry::new(cx.early_cx(), idx, sort, None);
                if !filter_unit || !matches!(entry, ListEntry::Unit) {
                    idx += 1;
                }
                (param.name(), entry)
            })
            .collect();
        Self::List(map)
    }

    fn single(cx: &ConvCtxt, param: &fhir::RefineParam) -> Self {
        let sort = cx.resolve_param_sort(param);
        let conv = conv_sort(cx.early_cx(), &sort);
        Self::Single(param.ident.name, sort, conv)
    }

    fn empty() -> Self {
        Self::List(FxIndexMap::default())
    }

    fn get(&self, name: impl Borrow<fhir::Name>, level: u32) -> Option<LookupResultKind> {
        match self {
            Layer::List(map) => {
                Some(LookupResultKind::LateBoundList { level, entry: map.get(name.borrow())? })
            }
            Layer::Single(bname, sort, conv) => {
                if bname == name.borrow() {
                    Some(LookupResultKind::LateBoundSingle { level, sort, conv })
                } else {
                    None
                }
            }
        }
    }

    fn into_fun_params(self) -> impl Iterator<Item = (rty::Sort, rty::InferMode)> {
        match self {
            Layer::List(map) => {
                map.into_values().filter_map(|entry| {
                    if let ListEntry::Sort { infer_mode, conv, .. } = entry {
                        Some((conv, infer_mode))
                    } else {
                        None
                    }
                })
            }
            _ => bug!(),
        }
    }

    fn into_sort(self) -> rty::Sort {
        match self {
            Layer::List(map) => {
                let sorts = map
                    .into_values()
                    .filter_map(|entry| {
                        if let ListEntry::Sort { conv, .. } = entry {
                            Some(conv)
                        } else {
                            None
                        }
                    })
                    .collect_vec();
                rty::Sort::tuple(sorts)
            }
            Layer::Single(_, _, conv) => conv,
        }
    }

    fn to_sort(&self) -> rty::Sort {
        match self {
            Layer::List(map) => {
                let sorts = map
                    .values()
                    .filter_map(|entry| {
                        if let ListEntry::Sort { conv, .. } = entry {
                            Some(conv.clone())
                        } else {
                            None
                        }
                    })
                    .collect_vec();
                rty::Sort::tuple(sorts)
            }
            Layer::Single(_, _, conv) => conv.clone(),
        }
    }
}

impl ListEntry {
    fn new(
        early_cx: &EarlyCtxt,
        idx: u32,
        sort: fhir::Sort,
        infer_mode: Option<fhir::InferMode>,
    ) -> Self {
        let conv = conv_sort(early_cx, &sort);
        if conv.is_unit() {
            ListEntry::Unit
        } else {
            let infer_mode = infer_mode.unwrap_or_else(|| conv.default_infer_mode());
            ListEntry::Sort { sort, infer_mode, conv, idx }
        }
    }
}

impl LookupResult<'_> {
    fn to_expr(&self) -> rty::Expr {
        match &self.kind {
            LookupResultKind::LateBoundList { level, entry: ListEntry::Sort { idx, conv, .. } } => {
                rty::Expr::tuple_proj(rty::Expr::late_bvar(DebruijnIndex::new(*level)), *idx)
                    .eta_expand_tuple(conv)
            }
            LookupResultKind::LateBoundList { entry: ListEntry::Unit, .. } => rty::Expr::unit(),
            LookupResultKind::LateBoundSingle { level, conv, .. } => {
                rty::Expr::late_bvar(DebruijnIndex::new(*level)).eta_expand_tuple(conv)
            }
            LookupResultKind::EarlyBound { idx, conv, .. } => {
                rty::Expr::early_bvar(*idx).eta_expand_tuple(conv)
            }
        }
    }

    fn is_record(&self) -> Option<DefId> {
        match &self.kind {
            LookupResultKind::LateBoundSingle { sort: fhir::Sort::Record(def_id), .. } => {
                Some(*def_id)
            }
            LookupResultKind::LateBoundList {
                entry: ListEntry::Sort { sort: fhir::Sort::Record(def_id), .. },
                ..
            } => Some(*def_id),
            LookupResultKind::EarlyBound { sort: fhir::Sort::Record(def_id), .. } => Some(*def_id),
            _ => None,
        }
    }

    fn to_path(&self) -> rty::Path {
        self.to_expr().to_path().unwrap_or_else(|| {
            span_bug!(self.name.span(), "expected path, found `{:?}`", self.to_expr())
        })
    }

    fn get_field(&self, early_cx: &EarlyCtxt, fld: SurfaceIdent) -> rty::Expr {
        if let Some(def_id) = self.is_record() {
            let i = early_cx
                .field_index(def_id, fld.name)
                .unwrap_or_else(|| span_bug!(fld.span, "field not found `{fld:?}`"));
            rty::Expr::tuple_proj(self.to_expr(), i as u32)
        } else {
            span_bug!(fld.span, "expected record sort")
        }
    }
}

pub fn conv_func_decl(early_cx: &EarlyCtxt, uif: &fhir::FuncDecl) -> rty::FuncDecl {
    rty::FuncDecl { name: uif.name, sort: conv_func_sort(early_cx, &uif.sort), kind: uif.kind }
}

fn conv_sorts<'a>(
    early_cx: &EarlyCtxt,
    sorts: impl IntoIterator<Item = &'a fhir::Sort>,
) -> Vec<rty::Sort> {
    sorts
        .into_iter()
        .map(|sort| conv_sort(early_cx, sort))
        .collect()
}

fn conv_sort(early_cx: &EarlyCtxt, sort: &fhir::Sort) -> rty::Sort {
    match sort {
        fhir::Sort::Int => rty::Sort::Int,
        fhir::Sort::Real => rty::Sort::Real,
        fhir::Sort::Bool => rty::Sort::Bool,
        fhir::Sort::BitVec(w) => rty::Sort::BitVec(*w),
        fhir::Sort::Loc => rty::Sort::Loc,
        fhir::Sort::Unit => rty::Sort::unit(),
        fhir::Sort::User(name) => rty::Sort::User(*name),
        fhir::Sort::Func(fsort) => rty::Sort::Func(conv_func_sort(early_cx, fsort)),
        fhir::Sort::Record(def_id) => {
            rty::Sort::tuple(conv_sorts(early_cx, early_cx.index_sorts_of(*def_id)))
        }
        fhir::Sort::Param(def_id) => {
            rty::Sort::Param(def_id_to_param_ty(early_cx.tcx, def_id.expect_local()))
        }
        fhir::Sort::Wildcard | fhir::Sort::Infer(_) => bug!("unexpected sort `{sort:?}`"),
    }
}

fn conv_func_sort(early_cx: &EarlyCtxt, fsort: &fhir::FuncSort) -> rty::FuncSort {
    rty::FuncSort::new(
        rty::Sort::tuple(conv_sorts(early_cx, fsort.inputs())),
        conv_sort(early_cx, fsort.output()),
    )
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(r),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}

fn def_id_to_param_ty(tcx: TyCtxt, def_id: LocalDefId) -> rty::ParamTy {
    let item_def_id = tcx.hir().ty_param_owner(def_id);
    let generics = tcx.generics_of(item_def_id);
    let index = generics.param_def_id_to_index[&def_id.to_def_id()];
    rty::ParamTy { index, name: tcx.hir().ty_param_name(def_id) }
}
