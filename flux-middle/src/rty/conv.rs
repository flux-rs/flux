//! Conversion types in [`crate::fhir`] to types in [`crate::rty`]
//!
//! Conversion assumes well-formedness and will panic if they are not.  Well-formedness implies
//! among other things:
//! 1. Names are bound correctly
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`crate::rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted
use std::{borrow::Borrow, iter, ops::Range};

use flux_common::bug;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use super::{fold::TypeFoldable, Binders, PolyVariant};
use crate::{
    early_ctxt::EarlyCtxt,
    fhir,
    global_env::GlobalEnv,
    intern::List,
    rty::{self, DebruijnIndex},
    rustc::ty::GenericParamDefKind,
};

pub struct ConvCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    env: Env<'a, 'tcx>,
}

struct Env<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    layers: Vec<Layer>,
}

struct Layer {
    map: FxHashMap<fhir::Name, (fhir::Sort, Range<usize>)>,
}

pub(crate) fn expand_alias(genv: &GlobalEnv, alias: &fhir::Alias) -> rty::Binders<rty::Ty> {
    let mut cx = ConvCtxt::from_params(genv, &alias.params);
    let sorts = flatten_sorts(genv.early_cx(), genv.map().refined_by(alias.def_id).sorts());
    let ty = cx.conv_ty(&alias.ty);
    rty::Binders::new(ty, sorts)
}

pub(crate) fn adt_def_for_struct(
    early_cx: &EarlyCtxt,
    struct_def: &fhir::StructDef,
) -> rty::AdtDef {
    let refined_by = early_cx.map.refined_by(struct_def.def_id);
    let env = Env::from_params(early_cx, &struct_def.params);
    let sorts = flatten_sorts(early_cx, refined_by.sorts());
    let invariants = env.conv_invariants(&sorts, &struct_def.invariants);

    rty::AdtDef::new(
        early_cx.tcx.adt_def(struct_def.def_id),
        sorts,
        invariants,
        struct_def.is_opaque(),
    )
}

pub(crate) fn adt_def_for_enum(early_cx: &EarlyCtxt, enum_def: &fhir::EnumDef) -> rty::AdtDef {
    let env = Env::from_params(early_cx, &enum_def.params);
    let sorts = flatten_sorts(early_cx, early_cx.map.refined_by(enum_def.def_id).sorts());
    let invariants = env.conv_invariants(&sorts, &enum_def.invariants);
    rty::AdtDef::new(early_cx.tcx.adt_def(enum_def.def_id), sorts, invariants, false)
}

pub(crate) fn conv_defn(early_cx: &EarlyCtxt, defn: &fhir::Defn) -> rty::Defn {
    let env = Env::from_params(early_cx, &defn.args);
    let sorts = flatten_sorts(early_cx, defn.args.iter().map(|(_, sort)| sort));
    let expr = Binders::new(env.conv_expr(&defn.expr), sorts);
    rty::Defn { name: defn.name, expr }
}

pub fn conv_qualifier(early_cx: &EarlyCtxt, qualifier: &fhir::Qualifier) -> rty::Qualifier {
    let env = Env::from_params(early_cx, &qualifier.args);
    let sorts = flatten_sorts(early_cx, qualifier.args.iter().map(|(_, sort)| sort));
    let body = Binders::new(env.conv_expr(&qualifier.expr), sorts);
    rty::Qualifier { name: qualifier.name.clone(), body, global: qualifier.global }
}

pub(crate) fn conv_fn_sig(genv: &GlobalEnv, fn_sig: &fhir::FnSig) -> rty::PolySig {
    let mut cx = ConvCtxt::from_fun_params(genv, &fn_sig.params);

    let mut requires = vec![];
    for constr in &fn_sig.requires {
        requires.push(cx.conv_constr(constr));
    }

    let mut args = vec![];
    for ty in &fn_sig.args {
        args.push(cx.conv_ty(ty));
    }

    let output = cx.conv_fn_output(&fn_sig.output);

    let sorts = flatten_sorts(genv.early_cx(), fn_sig.params.iter().map(|param| &param.sort));
    let modes = cx.conv_infer_modes(&fn_sig.params);
    rty::PolySig::new(rty::Binders::new(rty::FnSig::new(requires, args, output), sorts), modes)
}

impl<'a, 'tcx> ConvCtxt<'a, 'tcx> {
    fn from_params(genv: &'a GlobalEnv<'a, 'tcx>, params: &[(fhir::Ident, fhir::Sort)]) -> Self {
        let env = Env::from_params(genv.early_cx(), params);
        Self { genv, env }
    }

    fn from_fun_params(genv: &'a GlobalEnv<'a, 'tcx>, params: &[fhir::FunRefineParam]) -> Self {
        let env = Env::from_fun_params(genv.early_cx(), params);
        Self { genv, env }
    }

    fn conv_fn_output(&mut self, output: &fhir::FnOutput) -> Binders<rty::FnOutput> {
        self.env.push_layer(Layer::new(
            self.early_cx(),
            output
                .params
                .iter()
                .map(|param| (&param.name.name, &param.sort)),
        ));

        let ret = self.conv_ty(&output.ret);
        let ensures = output
            .ensures
            .iter()
            .map(|constr| self.conv_constr(constr))
            .collect_vec();
        let sorts = flatten_sorts(self.early_cx(), output.params.iter().map(|param| &param.sort));
        let output = rty::FnOutput::new(ret, ensures);

        self.env.pop_layer();

        Binders::new(output, sorts)
    }

    fn conv_infer_modes(&self, params: &[fhir::FunRefineParam]) -> Vec<rty::InferMode> {
        params
            .iter()
            .flat_map(|param| {
                let n = if let fhir::Sort::Aggregate(def_id) = &param.sort {
                    self.early_cx().index_sorts_of(*def_id).len()
                } else {
                    1
                };
                (0..n).map(|_| param.mode)
            })
            .collect()
    }

    pub(crate) fn conv_enum_def_variants(
        genv: &GlobalEnv,
        enum_def: &fhir::EnumDef,
    ) -> Vec<PolyVariant> {
        enum_def
            .variants
            .iter()
            .map(|variant_def| ConvCtxt::conv_variant(genv, variant_def))
            .collect()
    }

    fn conv_variant(genv: &GlobalEnv, variant: &fhir::VariantDef) -> PolyVariant {
        let mut cx = ConvCtxt::from_fun_params(genv, &variant.params);
        let fields = variant.fields.iter().map(|ty| cx.conv_ty(ty)).collect_vec();
        let sorts = flatten_sorts(genv.early_cx(), variant.params.iter().map(|param| &param.sort));
        let args =
            rty::RefineArgs::new(cx.conv_refine_arg(&variant.ret.idx, &variant.ret.bty.sort()));
        let ret = cx.conv_base_ty(&variant.ret.bty, args);
        let variant = rty::VariantDef::new(fields, ret);
        Binders::new(variant, sorts)
    }

    pub(crate) fn conv_struct_def_variant(
        genv: &GlobalEnv,
        struct_def: &fhir::StructDef,
    ) -> Option<rty::PolyVariant> {
        let mut cx = ConvCtxt::from_params(genv, &struct_def.params);

        let def_id = struct_def.def_id;
        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let fields = fields.iter().map(|ty| cx.conv_ty(ty)).collect_vec();

            let substs = genv
                .generics_of(def_id)
                .params
                .iter()
                .map(|param| {
                    match param.kind {
                        GenericParamDefKind::Type { .. } => {
                            rty::GenericArg::Ty(rty::Ty::param(rty::ParamTy {
                                index: param.index,
                                name: param.name,
                            }))
                        }
                        GenericParamDefKind::Lifetime => rty::GenericArg::Lifetime,
                    }
                })
                .collect_vec();

            let sorts = flatten_sorts(genv.early_cx(), genv.map().refined_by(def_id).sorts());
            let ret = rty::Ty::indexed(
                rty::BaseTy::adt(genv.adt_def(def_id), substs),
                rty::RefineArgs::bound(sorts.len()),
            );
            let variant = rty::VariantDef::new(fields, ret);
            Some(Binders::new(variant, sorts))
        } else {
            None
        }
    }

    fn conv_constr(&mut self, constr: &fhir::Constraint) -> rty::Constraint {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                rty::Constraint::Type(
                    self.env.expect_one_var(loc.name).to_var().to_path(),
                    self.conv_ty(ty),
                )
            }
            fhir::Constraint::Pred(pred) => rty::Constraint::Pred(self.env.conv_expr(pred)),
        }
    }

    fn conv_ty(&mut self, ty: &fhir::Ty) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                let sorts = flatten_sort(self.early_cx(), &bty.sort());
                if sorts.is_empty() {
                    self.conv_base_ty(bty, rty::RefineArgs::empty())
                } else {
                    self.env.push_layer(Layer::empty());
                    let ty = self.conv_base_ty(bty, rty::RefineArgs::bound(sorts.len()));
                    self.env.pop_layer();
                    rty::Ty::exists(Binders::new(ty, sorts))
                }
            }
            fhir::Ty::Indexed(bty, idx) => {
                let idxs = rty::RefineArgs::new(self.conv_refine_arg(idx, &bty.sort()));
                self.conv_base_ty(bty, idxs)
            }
            fhir::Ty::Exists(bty, bind, pred) => {
                let sorts = flatten_sort(self.early_cx(), &bty.sort());
                self.env
                    .push_layer(Layer::new(self.early_cx(), [(&bind.name, &bty.sort())]));
                let ty = self.conv_base_ty(bty, rty::RefineArgs::bound(sorts.len()));
                let pred = self.env.conv_expr(pred);
                self.env.pop_layer();
                rty::Ty::exists(Binders::new(rty::Ty::constr(pred, ty), sorts))
            }
            fhir::Ty::Ptr(loc) => {
                rty::Ty::ptr(
                    rty::RefKind::Mut,
                    self.env.expect_one_var(loc.name).to_var().to_path(),
                )
            }
            fhir::Ty::Ref(rk, ty) => rty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(ty)),
            fhir::Ty::Param(def_id) => {
                let def_id = def_id.expect_local();
                let item_def_id = self.genv.hir().ty_param_owner(def_id);
                let generics = self.genv.generics_of(item_def_id);
                let index = generics.rustc.param_def_id_to_index[&def_id.to_def_id()];
                let param_ty = rty::ParamTy { index, name: self.genv.hir().ty_param_name(def_id) };
                rty::Ty::param(param_ty)
            }
            fhir::Ty::Float(float_ty) => rty::Ty::float(rustc_middle::ty::float_ty(*float_ty)),
            fhir::Ty::Tuple(tys) => {
                let tys = tys.iter().map(|ty| self.conv_ty(ty)).collect_vec();
                rty::Ty::tuple(tys)
            }
            fhir::Ty::Array(ty, len) => {
                rty::Ty::array(self.conv_ty(ty), rty::Const { val: len.val })
            }
            fhir::Ty::Never => rty::Ty::never(),
            fhir::Ty::Constr(pred, ty) => {
                let pred = self.env.conv_expr(pred);
                rty::Ty::constr(pred, self.conv_ty(ty))
            }

            fhir::Ty::Str => rty::Ty::str(),
            fhir::Ty::Char => rty::Ty::char(),
            fhir::Ty::RawPtr(ty, mutability) => {
                rty::Ty::indexed(
                    rty::BaseTy::RawPtr(self.conv_ty(ty), *mutability),
                    rty::RefineArgs::empty(),
                )
            }
        }
    }

    fn conv_refine_arg(
        &mut self,
        arg: &fhir::RefineArg,
        sort: &fhir::Sort,
    ) -> Vec<(rty::RefineArg, bool)> {
        let mut output = vec![];
        self.conv_refine_arg_aux(arg, sort, &mut output);
        output
    }

    fn conv_refine_arg_aux(
        &mut self,
        arg: &fhir::RefineArg,
        sort: &fhir::Sort,
        output: &mut Vec<(rty::RefineArg, bool)>,
    ) {
        match arg {
            fhir::RefineArg::Expr {
                expr: fhir::Expr { kind: fhir::ExprKind::Var(var), .. },
                is_binder,
            } => {
                let (_, bvars) = self.env.get(var.name);
                output.extend(
                    bvars
                        .into_iter()
                        .map(|bvar| (rty::RefineArg::Expr(bvar.to_expr()), *is_binder)),
                );
            }
            fhir::RefineArg::Expr { expr, is_binder } => {
                output.push((rty::RefineArg::Expr(self.env.conv_expr(expr)), *is_binder));
            }
            fhir::RefineArg::Abs(params, body, _) => {
                let fsort = self.expect_func(sort);
                self.env
                    .push_layer(Layer::new(self.early_cx(), iter::zip(params, fsort.inputs())));
                let pred = self.env.conv_expr(body);
                let abs = rty::Binders::new(pred, flatten_sorts(self.early_cx(), fsort.inputs()));
                self.env.pop_layer();
                output.push((rty::RefineArg::Abs(abs), false));
            }
            fhir::RefineArg::Aggregate(def_id, flds, _) => {
                let sorts = self.genv.index_sorts_of(*def_id);
                for (arg, sort) in iter::zip(flds, sorts) {
                    self.conv_refine_arg_aux(arg, sort, output);
                }
            }
        }
    }

    fn conv_ref_kind(rk: fhir::RefKind) -> rty::RefKind {
        match rk {
            fhir::RefKind::Mut => rty::RefKind::Mut,
            fhir::RefKind::Shr => rty::RefKind::Shr,
        }
    }

    fn conv_base_ty(&mut self, bty: &fhir::BaseTy, idx: rty::RefineArgs) -> rty::Ty {
        match bty {
            fhir::BaseTy::Path(path) => self.conv_path(path, idx),
            fhir::BaseTy::Slice(ty) => {
                let slice = rty::BaseTy::slice(self.conv_ty(ty));
                rty::Ty::indexed(slice, idx)
            }
        }
    }

    fn conv_path(&mut self, path: &fhir::Path, idx: rty::RefineArgs) -> rty::Ty {
        let bty = match &path.res {
            fhir::Res::Int(int_ty) => rty::BaseTy::Int(rustc_middle::ty::int_ty(*int_ty)),
            fhir::Res::Uint(uint_ty) => rty::BaseTy::Uint(rustc_middle::ty::uint_ty(*uint_ty)),
            fhir::Res::Bool => rty::BaseTy::Bool,
            fhir::Res::Adt(did) => {
                let substs = self.conv_generic_args(*did, &path.generics);
                let adt_def = self.genv.adt_def(*did);
                rty::BaseTy::adt(adt_def, substs)
            }
            fhir::Res::Alias(def_id, early) => {
                let mut args = vec![];
                for (arg, sort) in iter::zip(early, self.genv.early_bound_sorts_of(*def_id)) {
                    self.conv_refine_arg_aux(arg, sort, &mut args);
                }
                let args = args
                    .into_iter()
                    .map(|(arg, _)| arg)
                    .chain(idx.args().iter().cloned())
                    .collect_vec();
                return self
                    .genv
                    .type_of(*def_id)
                    .replace_generics(&self.conv_generic_args(*def_id, &path.generics))
                    .replace_bvars(&args);
            }
        };
        rty::Ty::indexed(bty, idx)
    }

    fn conv_generic_args(&mut self, def_id: DefId, args: &[fhir::Ty]) -> Vec<rty::GenericArg> {
        let mut i = 0;
        self.genv
            .generics_of(def_id)
            .params
            .iter()
            .map(|generic| {
                match &generic.kind {
                    GenericParamDefKind::Type { has_default } => {
                        if i < args.len() {
                            i += 1;
                            self.conv_generic_arg(&args[i - 1])
                        } else {
                            debug_assert!(has_default);
                            rty::GenericArg::Ty(self.genv.default_type_of(generic.def_id))
                        }
                    }
                    GenericParamDefKind::Lifetime => rty::GenericArg::Lifetime,
                }
            })
            .collect()
    }

    fn conv_generic_arg(&mut self, arg: &fhir::Ty) -> rty::GenericArg {
        rty::GenericArg::Ty(self.conv_ty(arg))
    }

    fn early_cx(&self) -> &EarlyCtxt<'a, 'tcx> {
        self.genv.early_cx()
    }

    fn expect_func(&self, sort: &fhir::Sort) -> fhir::FuncSort {
        self.early_cx().is_coercible_to_func(sort).unwrap()
    }
}

impl<'a, 'tcx> Env<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>, layer: Layer) -> Env<'a, 'tcx> {
        Self { early_cx, layers: vec![layer] }
    }

    fn from_params(early_cx: &'a EarlyCtxt<'a, 'tcx>, slice: &[(fhir::Ident, fhir::Sort)]) -> Self {
        Self::new(
            early_cx,
            Layer::new(early_cx, slice.iter().map(|(ident, sort)| (&ident.name, sort))),
        )
    }

    fn from_fun_params(early_cx: &'a EarlyCtxt<'a, 'tcx>, params: &[fhir::FunRefineParam]) -> Self {
        Self::new(
            early_cx,
            Layer::new(early_cx, params.iter().map(|param| (&param.name.name, &param.sort))),
        )
    }

    fn push_layer(&mut self, layer: Layer) {
        self.layers.push(layer);
    }

    fn pop_layer(&mut self) {
        self.layers.pop();
    }

    fn get(&self, name: impl Borrow<fhir::Name>) -> (&fhir::Sort, Vec<rty::BoundVar>) {
        for (level, layer) in self.layers.iter().rev().enumerate() {
            if let Some((sort, range)) = layer.get(name.borrow()) {
                let vars = range
                    .clone()
                    .map(|idx| rty::BoundVar::new(idx, DebruijnIndex::new(level as u32)))
                    .collect();
                return (sort, vars);
            }
        }
        panic!("no entry found for key: `{:?}`", name.borrow());
    }

    fn expect_one_var(&self, name: fhir::Name) -> rty::BoundVar {
        let (_, mut vars) = self.get(name);
        if vars.len() == 1 {
            vars.pop().unwrap()
        } else {
            todo!()
        }
    }
}

impl Env<'_, '_> {
    fn conv_expr(&self, expr: &fhir::Expr) -> rty::Expr {
        match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
            fhir::ExprKind::Var(var) => self.expect_one_var(var.name).to_expr(),
            fhir::ExprKind::Literal(lit) => rty::Expr::constant(conv_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                rty::Expr::binary_op(*op, self.conv_expr(e1), self.conv_expr(e2))
            }
            fhir::ExprKind::UnaryOp(op, e) => rty::Expr::unary_op(*op, self.conv_expr(e)),
            fhir::ExprKind::App(func, args) => {
                rty::Expr::app(self.conv_func(func), self.conv_exprs(args))
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                rty::Expr::ite(self.conv_expr(p), self.conv_expr(e1), self.conv_expr(e2))
            }
            fhir::ExprKind::Dot(var, fld) => {
                let (sort, vars) = self.get(var.name);
                if let fhir::Sort::Aggregate(def_id) = sort {
                    let idx = self
                        .early_cx
                        .field_index(*def_id, fld.name)
                        .unwrap_or_else(|| bug!("field not found `{fld:?}`"));
                    vars[idx].to_expr()
                } else {
                    todo!()
                }
            }
        }
    }

    fn conv_func(&self, func: &fhir::Func) -> rty::Func {
        match func {
            fhir::Func::Var(ident) => rty::Func::Var(self.expect_one_var(ident.name).to_var()),
            fhir::Func::Uif(sym, _) => rty::Func::Uif(*sym),
        }
    }

    fn conv_exprs(&self, exprs: &[fhir::Expr]) -> List<rty::Expr> {
        List::from_iter(exprs.iter().map(|e| self.conv_expr(e)))
    }

    fn conv_invariants(
        &self,
        sorts: &[rty::Sort],
        invariants: &[fhir::Expr],
    ) -> Vec<rty::Invariant> {
        invariants
            .iter()
            .map(|invariant| self.conv_invariant(sorts, invariant))
            .collect()
    }

    fn conv_invariant(&self, sorts: &[rty::Sort], invariant: &fhir::Expr) -> rty::Invariant {
        rty::Invariant { pred: Binders::new(self.conv_expr(invariant), sorts) }
    }
}

impl Layer {
    fn new<'a>(
        early_cx: &EarlyCtxt,
        iter: impl IntoIterator<Item = (&'a fhir::Name, &'a fhir::Sort)>,
    ) -> Self {
        let mut map = FxHashMap::default();
        let mut i = 0;
        for (name, sort) in iter.into_iter() {
            let nsorts = if let fhir::Sort::Aggregate(def_id) = sort {
                early_cx.index_sorts_of(*def_id).len()
            } else {
                1
            };
            map.insert(*name, (sort.clone(), i..(i + nsorts)));
            i += nsorts;
        }
        Self { map }
    }

    fn empty() -> Self {
        Self { map: FxHashMap::default() }
    }

    fn get(&self, name: impl Borrow<fhir::Name>) -> Option<&(fhir::Sort, Range<usize>)> {
        self.map.get(name.borrow())
    }
}

pub fn conv_uif(early_cx: &EarlyCtxt, uif: &fhir::UifDef) -> rty::UifDef {
    rty::UifDef { name: uif.name, sort: flatten_func_sort(early_cx, &uif.sort) }
}

fn flatten_sorts<'a>(
    early_cx: &EarlyCtxt,
    sorts: impl IntoIterator<Item = &'a fhir::Sort>,
) -> Vec<rty::Sort> {
    sorts
        .into_iter()
        .flat_map(|sort| flatten_sort(early_cx, sort))
        .collect()
}

fn flatten_sort(early_cx: &EarlyCtxt, sort: &fhir::Sort) -> Vec<rty::Sort> {
    match sort {
        fhir::Sort::Tuple(sorts) => {
            vec![rty::Sort::Tuple(List::from_vec(flatten_sorts(early_cx, sorts)))]
        }
        fhir::Sort::Func(fsort) => vec![rty::Sort::Func(flatten_func_sort(early_cx, fsort))],
        fhir::Sort::Aggregate(def_id) => flatten_sorts(early_cx, early_cx.index_sorts_of(*def_id)),
        fhir::Sort::Int
        | fhir::Sort::Real
        | fhir::Sort::Bool
        | fhir::Sort::Loc
        | fhir::Sort::User(_)
        | fhir::Sort::Infer => vec![sort.clone()],
    }
}

fn flatten_func_sort(early_cx: &EarlyCtxt, fsort: &fhir::FuncSort) -> rty::FuncSort {
    rty::FuncSort {
        inputs_and_output: List::from_vec(flatten_sorts(early_cx, fsort.inputs_and_output.iter())),
    }
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(r),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}
