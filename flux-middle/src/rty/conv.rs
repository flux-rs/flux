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
use rustc_target::abi::VariantIdx;

use super::{Binders, PolyVariant, VariantRet};
use crate::{
    early_ctxt::EarlyCtxt,
    fhir,
    global_env::GlobalEnv,
    intern::List,
    rty::{self, fold::TypeFoldable, DebruijnIndex},
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

pub(crate) fn conv_adt_def(early_cx: &EarlyCtxt, adt_def: &fhir::AdtDef) -> rty::AdtDef {
    let env = Env::from_refined_by(early_cx, &adt_def.refined_by);
    let sorts = flatten_sorts(early_cx, adt_def.refined_by.params.iter().map(|(_, sort)| sort));

    let invariants = adt_def
        .invariants
        .iter()
        .map(|invariant| env.conv_invariant(&sorts, invariant))
        .collect_vec();

    rty::AdtDef::new(early_cx.tcx.adt_def(adt_def.def_id), sorts, invariants, adt_def.opaque)
}

pub(crate) fn conv_defn(early_cx: &EarlyCtxt, defn: &fhir::Defn) -> rty::Defn {
    let env = Env::from_args(early_cx, &defn.args);
    let sorts = flatten_sorts(early_cx, defn.args.iter().map(|(_, sort)| sort));
    let expr = Binders::new(env.conv_expr(&defn.expr), sorts);
    rty::Defn { name: defn.name, expr }
}

impl<'a, 'tcx> ConvCtxt<'a, 'tcx> {
    fn from_refined_by(genv: &'a GlobalEnv<'a, 'tcx>, refined_by: &fhir::RefinedBy) -> Self {
        let env = Env::from_refined_by(genv.early_cx(), refined_by);
        Self { genv, env }
    }

    fn from_params(genv: &'a GlobalEnv<'a, 'tcx>, params: &[fhir::RefineParam]) -> Self {
        let env = Env::from_params(genv.early_cx(), params);
        Self { genv, env }
    }

    pub(crate) fn conv_fn_sig(genv: &GlobalEnv, fn_sig: &fhir::FnSig) -> rty::PolySig {
        let mut cx = ConvCtxt::from_params(genv, &fn_sig.params);

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

    fn conv_infer_modes(&self, params: &[fhir::RefineParam]) -> Vec<rty::InferMode> {
        params
            .iter()
            .flat_map(|param| {
                let n = if let fhir::Sort::Adt(def_id) = &param.sort {
                    self.early_cx().sorts_of(*def_id).len()
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
    ) -> Option<Vec<PolyVariant>> {
        let variants: Vec<PolyVariant> = enum_def
            .variants
            .iter()
            .map(|variant| ConvCtxt::conv_variant(genv, variant))
            .collect();

        // Return `None` if there are *no* refined variants as, in that case,
        // we want to fall back to using "default" `rustc` variant-signatures
        // at the match/downcast sites as done in `GlobalEnv::variant`.
        if variants.is_empty() {
            None
        } else {
            Some(variants)
        }
    }

    fn conv_variant(genv: &GlobalEnv, variant: &fhir::VariantDef) -> PolyVariant {
        let mut cx = ConvCtxt::from_params(genv, &variant.params);
        let fields = variant.fields.iter().map(|ty| cx.conv_ty(ty)).collect_vec();
        let sorts = flatten_sorts(genv.early_cx(), variant.params.iter().map(|param| &param.sort));
        let variant = rty::VariantDef::new(fields, cx.conv_variant_ret(&variant.ret));
        Binders::new(variant, sorts)
    }

    fn conv_variant_ret(&mut self, ret: &fhir::VariantRet) -> VariantRet {
        let bty = self.conv_base_ty(&ret.bty);
        let args = List::from_iter(
            iter::zip(ret.idx.flatten(), flatten_sort(self.early_cx(), &ret.bty.sort()))
                .flat_map(|(arg, sort)| self.conv_refine_arg(arg, &sort)),
        );

        VariantRet { bty, args }
    }

    pub(crate) fn conv_struct_def_variant(
        genv: &GlobalEnv,
        refined_by: &fhir::RefinedBy,
        struct_def: &fhir::StructDef,
    ) -> Option<rty::PolyVariant> {
        let mut cx = ConvCtxt::from_refined_by(genv, refined_by);

        let def_id = struct_def.def_id.to_def_id();
        let rustc_adt = genv.tcx.adt_def(def_id);
        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let fields = iter::zip(fields, &rustc_adt.variant(VariantIdx::from_u32(0)).fields)
                .map(|(ty, field)| {
                    match ty {
                        Some(ty) => cx.conv_ty(ty),
                        None => genv.default_type_of(field.did),
                    }
                })
                .collect_vec();

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

            let sorts = flatten_sorts(genv.early_cx(), refined_by.sorts());
            let idxs =
                (0..sorts.len()).map(|idx| rty::Expr::bvar(rty::BoundVar::innermost(idx)).into());
            let ret = VariantRet {
                bty: rty::BaseTy::adt(genv.adt_def(def_id), substs),
                args: List::from_iter(idxs),
            };
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

    pub fn conv_qualifier(early_cx: &EarlyCtxt, qualifier: &fhir::Qualifier) -> rty::Qualifier {
        let env = Env::from_args(early_cx, &qualifier.args);
        let sorts = flatten_sorts(early_cx, qualifier.args.iter().map(|(_, sort)| sort));
        let body = Binders::new(env.conv_expr(&qualifier.expr), sorts);
        rty::Qualifier { name: qualifier.name.clone(), body, global: qualifier.global }
    }

    fn conv_ty(&mut self, ty: &fhir::Ty) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                if flatten_sort(self.early_cx(), &bty.sort()).is_empty() {
                    let bty = self.conv_base_ty(bty);
                    rty::Ty::indexed(bty, rty::RefineArgs::empty())
                } else {
                    self.env.push_layer(Layer::empty());
                    let bty = self.conv_base_ty(bty);
                    self.env.pop_layer();
                    rty::Ty::full_exists(bty, rty::Expr::tt())
                }
            }
            fhir::Ty::Indexed(bty, idx) => self.conv_indexed(bty, idx),
            fhir::Ty::Exists(bty, bind, pred) => {
                self.env
                    .push_layer(Layer::new(self.early_cx(), [(&bind.name, &bty.sort())]));
                let bty = self.conv_base_ty(bty);
                let pred = self.env.conv_expr(pred);
                self.env.pop_layer();
                rty::Ty::full_exists(bty, pred)
            }
            fhir::Ty::Ptr(loc) => {
                rty::Ty::ptr(
                    rty::RefKind::Mut,
                    self.env.expect_one_var(loc.name).to_var().to_path(),
                )
            }
            fhir::Ty::Ref(rk, ty) => rty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(ty)),
            fhir::Ty::Param(param) => rty::Ty::param(*param),
            fhir::Ty::Float(float_ty) => rty::Ty::float(*float_ty),
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
            fhir::Ty::Alias(def_id, args) => {
                self.genv
                    .default_type_of(*def_id)
                    .replace_generics(&self.conv_generic_args(*def_id, args))
            }
        }
    }

    fn conv_indexed(&mut self, bty: &fhir::BaseTy, idx: &fhir::Index) -> rty::Ty {
        let mut args = vec![];
        for (arg, sort) in iter::zip(idx.flatten(), flatten_sort(self.early_cx(), &bty.sort())) {
            let is_binder = matches!(arg, fhir::RefineArg::Expr { is_binder: true, .. });
            args.extend(
                self.conv_refine_arg(arg, &sort)
                    .into_iter()
                    .map(|arg| (arg, is_binder)),
            );
        }
        let args = rty::RefineArgs::new(args);
        let bty = self.conv_base_ty(bty);
        rty::Ty::indexed(bty, args)
    }

    fn conv_refine_arg(&mut self, arg: &fhir::RefineArg, sort: &fhir::Sort) -> Vec<rty::RefineArg> {
        match arg {
            fhir::RefineArg::Expr {
                expr: fhir::Expr { kind: fhir::ExprKind::Var(var), .. },
                ..
            } => {
                let (_, bvars) = self.env.get(var.name);
                bvars
                    .into_iter()
                    .map(|bvar| rty::RefineArg::Expr(bvar.to_expr()))
                    .collect_vec()
            }
            fhir::RefineArg::Expr { expr, .. } => {
                vec![rty::RefineArg::Expr(self.env.conv_expr(expr))]
            }
            fhir::RefineArg::Abs(params, body, _) => {
                let fsort = sort.as_func();
                self.env
                    .push_layer(Layer::new(self.early_cx(), iter::zip(params, fsort.inputs())));
                let pred = self.env.conv_expr(body);
                let abs = rty::Binders::new(pred, flatten_sorts(self.early_cx(), fsort.inputs()));
                self.env.pop_layer();
                vec![rty::RefineArg::Abs(abs)]
            }
        }
    }

    fn conv_ref_kind(rk: fhir::RefKind) -> rty::RefKind {
        match rk {
            fhir::RefKind::Mut => rty::RefKind::Mut,
            fhir::RefKind::Shr => rty::RefKind::Shr,
        }
    }

    fn conv_base_ty(&mut self, bty: &fhir::BaseTy) -> rty::BaseTy {
        match bty {
            fhir::BaseTy::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            fhir::BaseTy::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            fhir::BaseTy::Bool => rty::BaseTy::Bool,
            fhir::BaseTy::Slice(ty) => rty::BaseTy::slice(self.conv_ty(ty)),
            fhir::BaseTy::Adt(did, args) => {
                let substs = self.conv_generic_args(*did, args);
                let adt_def = self.genv.adt_def(*did);
                rty::BaseTy::adt(adt_def, substs)
            }
        }
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
}

impl<'a, 'tcx> Env<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>, layer: Layer) -> Env<'a, 'tcx> {
        Self { early_cx, layers: vec![layer] }
    }

    fn from_args(early_cx: &'a EarlyCtxt<'a, 'tcx>, slice: &[(fhir::Ident, fhir::Sort)]) -> Self {
        Self::new(
            early_cx,
            Layer::new(early_cx, slice.iter().map(|(ident, sort)| (&ident.name, sort))),
        )
    }

    fn from_params(early_cx: &'a EarlyCtxt<'a, 'tcx>, params: &[fhir::RefineParam]) -> Self {
        Self::new(
            early_cx,
            Layer::new(early_cx, params.iter().map(|param| (&param.name.name, &param.sort))),
        )
    }

    fn from_refined_by(early_cx: &'a EarlyCtxt<'a, 'tcx>, refined_by: &fhir::RefinedBy) -> Self {
        Self::new(
            early_cx,
            Layer::new(
                early_cx,
                refined_by
                    .params
                    .iter()
                    .map(|(ident, sort)| (&ident.name, sort)),
            ),
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
                if let fhir::Sort::Adt(def_id) = sort {
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
            let nsorts = if let fhir::Sort::Adt(def_id) = sort {
                early_cx.sorts_of(*def_id).len()
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
        fhir::Sort::Adt(def_id) => flatten_sorts(early_cx, early_cx.sorts_of(*def_id)),
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
