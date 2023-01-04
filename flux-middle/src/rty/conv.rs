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
    env: Env,
}

struct Env {
    layers: Vec<Layer>,
}

struct Layer {
    names: FxHashMap<fhir::Name, Range<usize>>,
}

pub(crate) fn conv_adt_def(tcx: TyCtxt, adt_def: &fhir::AdtDef) -> rty::AdtDef {
    let env = Env::from_refined_by(&adt_def.refined_by);
    let sorts = conv_sorts(adt_def.refined_by.params.iter().map(|(_, sort)| sort));

    let invariants = adt_def
        .invariants
        .iter()
        .map(|invariant| env.conv_invariant(&sorts, invariant))
        .collect_vec();

    rty::AdtDef::new(tcx.adt_def(adt_def.def_id), sorts, invariants, adt_def.opaque)
}

pub(crate) fn conv_defn(defn: &fhir::Defn) -> rty::Defn {
    let env = Env::from_args(&defn.args);
    let sorts = conv_sorts(defn.args.iter().map(|(_, sort)| sort));
    let expr = Binders::new(env.conv_expr(&defn.expr), sorts);
    rty::Defn { name: defn.name, expr }
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    fn from_refined_by(genv: &'a GlobalEnv<'genv, 'tcx>, refined_by: &fhir::RefinedBy) -> Self {
        let env = Env::from_refined_by(refined_by);
        Self { genv, env }
    }

    fn from_params(genv: &'a GlobalEnv<'genv, 'tcx>, params: &[fhir::RefineParam]) -> Self {
        let env = Env::from_params(params);
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

        let sorts = conv_sorts(fn_sig.params.iter().map(|param| &param.sort));
        let modes = fn_sig.params.iter().map(|param| param.mode).collect_vec();
        rty::PolySig::new(
            rty::Binders::new(rty::FnSig::new(requires, args, ret, ensures), sorts),
            modes,
        )
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
        let sorts = conv_sorts(variant.params.iter().map(|param| &param.sort));
        let variant = rty::VariantDef::new(fields, cx.conv_variant_ret(&variant.ret));
        Binders::new(variant, sorts)
    }

    fn conv_variant_ret(&mut self, ret: &fhir::VariantRet) -> VariantRet {
        let bty = self.conv_base_ty(&ret.bty);
        let args = List::from_iter(
            iter::zip(&ret.indices.indices, ret.bty.sorts(self.genv.map()))
                .map(|(arg, sort)| self.conv_refine_arg(arg, sort)),
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

            let sorts = conv_sorts(refined_by.sorts());
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

    pub fn conv_qualifier(qualifier: &fhir::Qualifier) -> rty::Qualifier {
        let env = Env::from_args(&qualifier.args);
        let sorts = conv_sorts(qualifier.args.iter().map(|(_, sort)| sort));
        let body = Binders::new(env.conv_expr(&qualifier.expr), sorts);
        rty::Qualifier { name: qualifier.name.clone(), body }
    }

    fn conv_ty(&mut self, ty: &fhir::Ty) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                if bty.sorts(self.genv.map()).is_empty() {
                    let bty = self.conv_base_ty(bty);
                    rty::Ty::indexed(bty, rty::RefineArgs::empty())
                } else {
                    self.env.push_layer([]);
                    let bty = self.conv_base_ty(bty);
                    let ty = rty::Ty::full_exists(bty, rty::Expr::tt());
                    self.env.pop_layer();
                    ty
                }
            }
            fhir::Ty::Indexed(bty, idxs) => {
                let idxs = self.conv_indices(idxs, bty.sorts(self.genv.map()));
                let bty = self.conv_base_ty(bty);
                rty::Ty::indexed(bty, idxs)
            }
            fhir::Ty::Exists(bty, binders, pred) => {
                self.env
                    .push_layer(iter::zip(binders, bty.sorts(self.genv.map())));
                let bty = self.conv_base_ty(bty);
                let pred = self.env.conv_expr(pred);
                let ty = rty::Ty::full_exists(bty, pred);
                self.env.pop_layer();
                ty
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

    fn conv_indices(&mut self, idxs: &fhir::Indices, sorts: &[fhir::Sort]) -> rty::RefineArgs {
        rty::RefineArgs::new(iter::zip(&idxs.indices, sorts).map(|(arg, sort)| {
            let is_binder = matches!(arg, fhir::RefineArg::Expr { is_binder: true, .. });
            (self.conv_refine_arg(arg, sort), is_binder)
        }))
    }

    fn conv_refine_arg(&mut self, arg: &fhir::RefineArg, sort: &fhir::Sort) -> rty::RefineArg {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => rty::RefineArg::Expr(self.env.conv_expr(expr)),
            fhir::RefineArg::Abs(params, body, _) => {
                let fsort = sort.as_func();
                self.env.push_layer(iter::zip(params, fsort.inputs()));
                let pred = self.env.conv_expr(body);
                let abs = rty::Binders::new(pred, conv_sorts(fsort.inputs()));
                self.env.pop_layer();
                rty::RefineArg::Abs(abs)
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

impl Env {
    fn new(layer: Layer) -> Self {
        Self { layers: vec![layer] }
    }

    fn from_args(slice: &[(fhir::Ident, fhir::Sort)]) -> Self {
        Self::new(Layer::new(slice.iter().map(|(ident, sort)| (&ident.name, sort))))
    }

    fn from_params(params: &[fhir::RefineParam]) -> Self {
        Self::new(Layer::new(params.iter().map(|param| (&param.name.name, &param.sort))))
    }

    fn from_refined_by(refined_by: &fhir::RefinedBy) -> Self {
        Self::new(Layer::new(
            refined_by
                .params
                .iter()
                .map(|(ident, sort)| (&ident.name, sort)),
        ))
    }

    fn push_layer<'a>(
        &mut self,
        binders: impl IntoIterator<Item = (&'a fhir::Name, &'a fhir::Sort)>,
    ) {
        self.layers.push(Layer::new(binders));
    }

    fn pop_layer(&mut self) {
        self.layers.pop();
    }

    fn get_bvars(&self, name: fhir::Name) -> Vec<rty::BoundVar> {
        for (level, layer) in self.layers.iter().rev().enumerate() {
            if let Some(range) = layer.get(&name) {
                return range
                    .clone()
                    .map(|idx| rty::BoundVar::new(idx, DebruijnIndex::new(level as u32)))
                    .collect();
            }
        }
        panic!("no entry found for key: `{name:?}`");
    }

    fn expect_one_var(&self, name: fhir::Name) -> rty::BoundVar {
        let mut vars = self.get_bvars(name);
        if vars.len() == 1 {
            vars.pop().unwrap()
        } else {
            todo!()
        }
    }
}

impl Env {
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
            fhir::ExprKind::Dot(_var, _fld, _) => {
                todo!()
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
    fn new<'a>(iter: impl IntoIterator<Item = (&'a fhir::Name, &'a fhir::Sort)>) -> Self {
        let mut names = FxHashMap::default();
        let mut i = 0;
        for (name, sort) in iter.into_iter() {
            let nsorts = conv_sort(sort).len();
            names.insert(*name, i..(i + nsorts));
            i += nsorts;
        }
        Self { names }
    }

    fn get(&self, name: impl Borrow<fhir::Name>) -> Option<&Range<usize>> {
        self.names.get(name.borrow())
    }
}

pub fn conv_uif(uif: &fhir::UifDef) -> rty::UifDef {
    rty::UifDef { name: uif.name, sort: conv_func_sort(&uif.sort) }
}

fn conv_sorts<'a>(sorts: impl IntoIterator<Item = &'a fhir::Sort>) -> Vec<rty::Sort> {
    sorts.into_iter().flat_map(conv_sort).collect()
}

fn conv_sort(sort: &fhir::Sort) -> Vec<rty::Sort> {
    match sort {
        fhir::Sort::Int => vec![rty::Sort::Int],
        fhir::Sort::Bool => vec![rty::Sort::Bool],
        fhir::Sort::Loc => vec![rty::Sort::Loc],
        fhir::Sort::Tuple(sorts) => vec![rty::Sort::Tuple(List::from_vec(conv_sorts(sorts)))],
        fhir::Sort::Func(fsort) => vec![rty::Sort::Func(conv_func_sort(fsort))],
        fhir::Sort::Infer => unreachable!("sorts must be known at this point"),
        fhir::Sort::Adt(_) => todo!(),
    }
}

fn conv_func_sort(fsort: &fhir::FuncSort) -> rty::FuncSort {
    rty::FuncSort { inputs_and_output: List::from_vec(conv_sorts(fsort.inputs_and_output.iter())) }
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}
