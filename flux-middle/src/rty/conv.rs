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

use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_target::abi::VariantIdx;

use super::{Binders, PolyVariant, VariantRet};
use crate::{
    fhir,
    global_env::GlobalEnv,
    intern::List,
    rty::{self, DebruijnIndex},
    rustc::ty::GenericParamDefKind,
};

pub struct ConvCtxt<'a, 'genv, 'tcx> {
    genv: &'a GlobalEnv<'genv, 'tcx>,
    env: Env<'a>,
}

struct Env<'a> {
    map: &'a fhir::Map,
    layers: Vec<Layer>,
}

struct Layer {
    map: FxHashMap<fhir::Name, (fhir::Sort, Range<usize>)>,
}

pub(crate) fn conv_adt_def(tcx: TyCtxt, map: &fhir::Map, adt_def: &fhir::AdtDef) -> rty::AdtDef {
    let env = Env::from_refined_by(map, &adt_def.refined_by);
    let sorts = flatten_sorts(map, adt_def.refined_by.params.iter().map(|(_, sort)| sort));

    let invariants = adt_def
        .invariants
        .iter()
        .map(|invariant| env.conv_invariant(&sorts, invariant))
        .collect_vec();

    rty::AdtDef::new(tcx.adt_def(adt_def.def_id), sorts, invariants, adt_def.opaque)
}

pub(crate) fn conv_defn(map: &fhir::Map, defn: &fhir::Defn) -> rty::Defn {
    let env = Env::from_args(map, &defn.args);
    let sorts = flatten_sorts(map, defn.args.iter().map(|(_, sort)| sort));
    let expr = Binders::new(env.conv_expr(&defn.expr), sorts);
    rty::Defn { name: defn.name, expr }
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    fn from_refined_by(genv: &'a GlobalEnv<'genv, 'tcx>, refined_by: &fhir::RefinedBy) -> Self {
        let env = Env::from_refined_by(genv.map(), refined_by);
        Self { genv, env }
    }

    fn from_params(genv: &'a GlobalEnv<'genv, 'tcx>, params: &[fhir::RefineParam]) -> Self {
        let env = Env::from_params(genv.map(), params);
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

        let mut ensures = vec![];
        for constr in &fn_sig.ensures {
            ensures.push(cx.conv_constr(constr));
        }

        let ret = cx.conv_ty(&fn_sig.ret);

        let sorts = flatten_sorts(genv.map(), fn_sig.params.iter().map(|param| &param.sort));
        let modes = cx.conv_infer_modes(&fn_sig.params);
        rty::PolySig::new(
            rty::Binders::new(rty::FnSig::new(requires, args, ret, ensures), sorts),
            modes,
        )
    }

    fn conv_infer_modes(&self, params: &[fhir::RefineParam]) -> Vec<rty::InferMode> {
        params
            .iter()
            .flat_map(|param| {
                let n = if let fhir::Sort::Adt(def_id) = &param.sort {
                    self.genv.map().sorts_of(*def_id).unwrap_or(&[]).len()
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
        let sorts = flatten_sorts(genv.map(), variant.params.iter().map(|param| &param.sort));
        let variant = rty::VariantDef::new(fields, cx.conv_variant_ret(&variant.ret));
        Binders::new(variant, sorts)
    }

    fn conv_variant_ret(&mut self, ret: &fhir::VariantRet) -> VariantRet {
        let bty = self.conv_base_ty(&ret.bty);
        let args = List::from_iter(
            iter::zip(ret.idx.flatten(), flatten_sort(self.genv.map(), &ret.bty.sort()))
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

        let def_id = struct_def.def_id;
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
                .generics_of(struct_def.def_id)
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

            let sorts = flatten_sorts(genv.map(), refined_by.sorts());
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

    pub fn conv_qualifier(map: &fhir::Map, qualifier: &fhir::Qualifier) -> rty::Qualifier {
        let env = Env::from_args(map, &qualifier.args);
        let sorts = flatten_sorts(map, qualifier.args.iter().map(|(_, sort)| sort));
        let body = Binders::new(env.conv_expr(&qualifier.expr), sorts);
        rty::Qualifier { name: qualifier.name.clone(), body }
    }

    fn conv_ty(&mut self, ty: &fhir::Ty) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                if flatten_sort(self.genv.map(), &bty.sort()).is_empty() {
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
                    .push_layer(Layer::new(self.genv.map(), [(bind, &bty.sort())]));
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
        }
    }

    fn conv_indexed(&mut self, bty: &fhir::BaseTy, idx: &fhir::Index) -> rty::Ty {
        let mut args = vec![];
        for (arg, sort) in iter::zip(idx.flatten(), flatten_sort(self.genv.map(), &bty.sort())) {
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
                expr: fhir::Expr { kind: fhir::ExprKind::Var(name, ..), .. },
                ..
            } => {
                let (_, bvars) = self.env.get(name);
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
                    .push_layer(Layer::new(self.genv.map(), iter::zip(params, fsort.inputs())));
                let pred = self.env.conv_expr(body);
                let abs = rty::Binders::new(pred, flatten_sorts(self.genv.map(), fsort.inputs()));
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
            fhir::BaseTy::Adt(did, substs) => {
                let mut i = 0;
                let substs = List::from_vec(
                    self.genv
                        .generics_of(*did)
                        .params
                        .iter()
                        .map(|generic| {
                            match &generic.kind {
                                GenericParamDefKind::Type { has_default } => {
                                    if i < substs.len() {
                                        i += 1;
                                        self.conv_generic_arg(&substs[i - 1])
                                    } else {
                                        debug_assert!(has_default);
                                        rty::GenericArg::Ty(
                                            self.genv.default_type_of(generic.def_id),
                                        )
                                    }
                                }
                                GenericParamDefKind::Lifetime => rty::GenericArg::Lifetime,
                            }
                        })
                        .collect(),
                );
                let adt_def = self.genv.adt_def(*did);
                rty::BaseTy::adt(adt_def, substs)
            }
        }
    }

    fn conv_generic_arg(&mut self, arg: &fhir::Ty) -> rty::GenericArg {
        rty::GenericArg::Ty(self.conv_ty(arg))
    }
}

impl<'a> Env<'a> {
    fn new(map: &'a fhir::Map, layer: Layer) -> Env<'a> {
        Self { map, layers: vec![layer] }
    }

    fn from_args(map: &'a fhir::Map, slice: &[(fhir::Ident, fhir::Sort)]) -> Self {
        Self::new(map, Layer::new(map, slice.iter().map(|(ident, sort)| (&ident.name, sort))))
    }

    fn from_params(map: &'a fhir::Map, params: &[fhir::RefineParam]) -> Self {
        Self::new(map, Layer::new(map, params.iter().map(|param| (&param.name.name, &param.sort))))
    }

    fn from_refined_by(map: &'a fhir::Map, refined_by: &fhir::RefinedBy) -> Self {
        Self::new(
            map,
            Layer::new(
                map,
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

impl Env<'_> {
    fn conv_expr(&self, expr: &fhir::Expr) -> rty::Expr {
        match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
            fhir::ExprKind::Var(name, ..) => self.expect_one_var(*name).to_expr(),
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
            fhir::ExprKind::Dot(var, fld, _) => {
                let (sort, vars) = self.get(var.name);
                if let fhir::Sort::Adt(def_id) = sort {
                    let idx = self
                        .map
                        .adt(def_id.expect_local())
                        .field_index(*fld)
                        .unwrap_or_else(|| panic!("field not found `{fld:?}`"));
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
        fhir_map: &fhir::Map,
        iter: impl IntoIterator<Item = (&'a fhir::Name, &'a fhir::Sort)>,
    ) -> Self {
        let mut map = FxHashMap::default();
        let mut i = 0;
        for (name, sort) in iter.into_iter() {
            let nsorts = if let fhir::Sort::Adt(def_id) = sort {
                fhir_map.sorts_of(*def_id).unwrap_or(&[]).len()
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

pub fn conv_uif(map: &fhir::Map, uif: &fhir::UifDef) -> rty::UifDef {
    rty::UifDef { name: uif.name, sort: flatten_func_sort(map, &uif.sort) }
}

fn flatten_sorts<'a>(
    map: &fhir::Map,
    sorts: impl IntoIterator<Item = &'a fhir::Sort>,
) -> Vec<rty::Sort> {
    sorts
        .into_iter()
        .flat_map(|sort| flatten_sort(map, sort))
        .collect()
}

fn flatten_sort(map: &fhir::Map, sort: &fhir::Sort) -> Vec<rty::Sort> {
    match sort {
        fhir::Sort::Int => vec![rty::Sort::Int],
        fhir::Sort::Bool => vec![rty::Sort::Bool],
        fhir::Sort::Loc => vec![rty::Sort::Loc],
        fhir::Sort::Tuple(sorts) => {
            vec![rty::Sort::Tuple(List::from_vec(flatten_sorts(map, sorts)))]
        }
        fhir::Sort::Func(fsort) => vec![rty::Sort::Func(flatten_func_sort(map, fsort))],
        fhir::Sort::Adt(def_id) => flatten_sorts(map, map.sorts_of(*def_id).unwrap_or(&[])),
        fhir::Sort::Infer => unreachable!("sorts must be known at this point"),
    }
}

fn flatten_func_sort(map: &fhir::Map, fsort: &fhir::FuncSort) -> rty::FuncSort {
    rty::FuncSort {
        inputs_and_output: List::from_vec(flatten_sorts(map, fsort.inputs_and_output.iter())),
    }
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}
