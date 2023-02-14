//! Conversion from types in [`crate::fhir`] to types in [`crate::rty`]
//!
//! Conversion assumes well-formedness and will panic if type are not well-formed. Among other things,
//! well-formedness implies:
//! 1. Names are bound correctly.
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`crate::rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted.
use std::{borrow::Borrow, iter};

use flux_common::span_bug;
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::def_id::DefId;

use super::{fold::TypeFoldable, Binder, PolyVariant};
use crate::{
    early_ctxt::EarlyCtxt,
    fhir::{self, SurfaceIdent},
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
    map: FxIndexMap<fhir::Name, LayerEntry>,
}

struct LayerEntry {
    sort: fhir::Sort,
    conv: rty::Sort,
}

struct LookupResult<'a> {
    name: fhir::Ident,
    idx: u32,
    level: u32,
    entry: &'a LayerEntry,
}

pub(crate) fn expand_ty_alias(genv: &GlobalEnv, alias: &fhir::TyAlias) -> rty::Binder<rty::Ty> {
    let mut cx = ConvCtxt::from_params(genv, &alias.params);
    let ty = cx.conv_ty(&alias.ty);
    let sorts = cx.env.pop_layer().into_sorts();
    rty::Binder::new(ty, rty::Sort::tuple(sorts))
}

pub(crate) fn adt_def_for_struct(
    early_cx: &EarlyCtxt,
    struct_def: &fhir::StructDef,
) -> rty::AdtDef {
    let env = Env::from_params(early_cx, &struct_def.params);
    let sorts = env.top_layer().to_sorts();
    let invariants = env.conv_invariants(&sorts, &struct_def.invariants);

    rty::AdtDef::new(
        early_cx.tcx.adt_def(struct_def.def_id),
        rty::Sort::tuple(sorts),
        invariants,
        struct_def.is_opaque(),
    )
}

pub(crate) fn adt_def_for_enum(early_cx: &EarlyCtxt, enum_def: &fhir::EnumDef) -> rty::AdtDef {
    let env = Env::from_params(early_cx, &enum_def.params);
    let sorts = env.top_layer().to_sorts();
    let invariants = env.conv_invariants(&sorts, &enum_def.invariants);
    rty::AdtDef::new(
        early_cx.tcx.adt_def(enum_def.def_id),
        rty::Sort::tuple(sorts),
        invariants,
        false,
    )
}

pub(crate) fn conv_defn(early_cx: &EarlyCtxt, defn: &fhir::Defn) -> rty::Defn {
    let mut env = Env::from_params(early_cx, &defn.args);
    let expr = env.conv_expr(&defn.expr);
    let expr = Binder::new(expr, rty::Sort::tuple(env.pop_layer().into_sorts()));
    rty::Defn { name: defn.name, expr }
}

pub fn conv_qualifier(early_cx: &EarlyCtxt, qualifier: &fhir::Qualifier) -> rty::Qualifier {
    let mut env = Env::from_params(early_cx, &qualifier.args);
    let body = env.conv_expr(&qualifier.expr);
    let body = Binder::new(body, rty::Sort::tuple(env.pop_layer().into_sorts()));
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

    let modes = cx.conv_infer_modes(&fn_sig.params);
    let sorts = cx.env.pop_layer().into_sorts();
    rty::PolySig::new(&sorts, rty::FnSig::new(requires, args, output), modes)
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

    fn conv_fn_output(&mut self, output: &fhir::FnOutput) -> Binder<rty::FnOutput> {
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
        let output = rty::FnOutput::new(ret, ensures);

        let sorts = self.env.pop_layer().into_sorts();

        Binder::new(output, rty::Sort::tuple(sorts))
    }

    fn conv_infer_modes(&self, params: &[fhir::FunRefineParam]) -> Vec<rty::InferMode> {
        params.iter().map(|param| param.mode).collect()
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
        let args = rty::Index::from(cx.conv_refine_arg(&variant.ret.idx, &variant.ret.bty.sort()));
        let ret = cx.conv_base_ty(&variant.ret.bty, args);
        let variant = rty::VariantDef::new(fields, ret);
        let sorts = cx.env.pop_layer().to_sorts();
        Binder::new(variant, rty::Sort::tuple(sorts))
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

            let sort = rty::Sort::tuple(cx.env.pop_layer().to_sorts());
            let ret = rty::Ty::indexed(
                rty::BaseTy::adt(genv.adt_def(def_id), substs),
                rty::Index::bound(&sort),
            );
            let variant = rty::VariantDef::new(fields, ret);
            Some(Binder::new(variant, sort))
        } else {
            None
        }
    }

    fn conv_constr(&mut self, constr: &fhir::Constraint) -> rty::Constraint {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                rty::Constraint::Type(self.env.lookup(*loc).to_path(), self.conv_ty(ty))
            }
            fhir::Constraint::Pred(pred) => rty::Constraint::Pred(self.env.conv_expr(pred)),
        }
    }

    fn conv_ty(&mut self, ty: &fhir::Ty) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                let sort = conv_sort(self.early_cx(), &bty.sort());
                if sort.is_unit() {
                    self.conv_base_ty(bty, rty::Index::unit())
                } else {
                    self.env.push_layer(Layer::empty());
                    let ty = self.conv_base_ty(bty, rty::Expr::nu().into());
                    self.env.pop_layer();
                    rty::Ty::exists(Binder::new(ty, sort))
                }
            }
            fhir::Ty::Indexed(bty, idx) => {
                let idxs = rty::Index::from(self.conv_refine_arg(idx, &bty.sort()));
                self.conv_base_ty(bty, idxs)
            }
            fhir::Ty::Exists(bty, bind, pred) => {
                let layer = Layer::new(self.early_cx(), [(&bind.name, &bty.sort())]);

                self.env.push_layer(layer);
                let idx = rty::Expr::tuple_proj(rty::Expr::nu(), 0).into();
                let ty = self.conv_base_ty(bty, idx);
                let pred = self.env.conv_expr(pred);
                let sorts = self.env.pop_layer().into_sorts();

                rty::Ty::exists(Binder::new(rty::Ty::constr(pred, ty), rty::Sort::tuple(sorts)))
            }
            fhir::Ty::Ptr(loc) => rty::Ty::ptr(rty::RefKind::Mut, self.env.lookup(*loc).to_path()),
            fhir::Ty::Ref(rk, ty) => rty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(ty)),
            fhir::Ty::Param(def_id) => {
                let def_id = def_id.expect_local();
                let item_def_id = self.genv.hir().ty_param_owner(def_id);
                let generics = self.genv.generics_of(item_def_id);
                let index = generics.rustc.param_def_id_to_index[&def_id.to_def_id()];
                let param_ty = rty::ParamTy { index, name: self.genv.hir().ty_param_name(def_id) };
                rty::Ty::param(param_ty)
            }
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
            fhir::Ty::RawPtr(ty, mutability) => {
                rty::Ty::indexed(
                    rty::BaseTy::RawPtr(self.conv_ty(ty), *mutability),
                    rty::Index::unit(),
                )
            }
        }
    }

    fn conv_refine_arg(
        &mut self,
        arg: &fhir::RefineArg,
        sort: &fhir::Sort,
    ) -> (rty::Expr, rty::TupleTree<bool>) {
        match arg {
            // fhir::RefineArg::Expr {
            //     expr: fhir::Expr { kind: fhir::ExprKind::Var(var), .. },
            //     is_binder,
            // } => {
            //     todo!()
            //     // output.extend(
            //     //     self.env
            //     //         .lookup(*var)
            //     //         .bvars()
            //     //         .map(|bvar| (bvar.to_expr(), *is_binder)),
            //     // );
            // }
            fhir::RefineArg::Expr { expr, is_binder } => {
                (self.env.conv_expr(expr), rty::TupleTree::Leaf(*is_binder))
            }
            fhir::RefineArg::Abs(params, body, _) => {
                let fsort = self.expect_func(sort);
                let params =
                    iter::zip(params, fsort.inputs()).map(|((name, _), sort)| (&name.name, sort));
                self.env.push_layer(Layer::new(self.early_cx(), params));
                let pred = self.env.conv_expr(body);
                let sorts = self.env.pop_layer().to_sorts();
                let body = rty::Binder::new(pred, rty::Sort::tuple(sorts));
                (rty::Expr::abs(body), rty::TupleTree::Leaf(false))
            }
            fhir::RefineArg::Aggregate(def_id, flds, _) => {
                let sorts = self.genv.index_sorts_of(*def_id);
                let mut exprs = vec![];
                let mut is_binder = vec![];
                for (arg, sort) in iter::zip(flds, sorts) {
                    let (e, i) = self.conv_refine_arg(arg, sort);
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

    fn conv_base_ty(&mut self, bty: &fhir::BaseTy, idx: rty::Index) -> rty::Ty {
        match bty {
            fhir::BaseTy::Path(path) => self.conv_path(path, idx),
            fhir::BaseTy::Slice(ty) => {
                let slice = rty::BaseTy::slice(self.conv_ty(ty));
                rty::Ty::indexed(slice, idx)
            }
        }
    }

    fn conv_path(&mut self, path: &fhir::Path, idx: rty::Index) -> rty::Ty {
        let bty = match &path.res {
            fhir::Res::Bool => rty::BaseTy::Bool,
            fhir::Res::Str => rty::BaseTy::Str,
            fhir::Res::Char => rty::BaseTy::Char,
            fhir::Res::Int(int_ty) => rty::BaseTy::Int(rustc_middle::ty::int_ty(*int_ty)),
            fhir::Res::Uint(uint_ty) => rty::BaseTy::Uint(rustc_middle::ty::uint_ty(*uint_ty)),
            fhir::Res::Float(float_ty) => rty::BaseTy::Float(rustc_middle::ty::float_ty(*float_ty)),
            fhir::Res::Adt(did) => {
                let substs = self.conv_generic_args(*did, &path.generics);
                let adt_def = self.genv.adt_def(*did);
                rty::BaseTy::adt(adt_def, substs)
            }
            fhir::Res::Alias(def_id, early) => {
                todo!()
                // let mut args = vec![];
                // for (arg, sort) in iter::zip(early, self.genv.early_bound_sorts_of(*def_id)) {
                //     let (expr, _) = self.conv_refine_arg(arg, sort);
                //     args.push(expr);
                // }
                // args.extend(idx.args().iter().cloned());
                // return self
                //     .genv
                //     .type_of(*def_id)
                //     .replace_generics(&self.conv_generic_args(*def_id, &path.generics))
                //     .replace_bvars(&args);
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

    fn pop_layer(&mut self) -> Layer {
        self.layers.pop().expect("bottom of layer stack")
    }

    fn top_layer(&self) -> &Layer {
        self.layers.last().expect("bottom of layer stack")
    }

    fn lookup(&self, name: fhir::Ident) -> LookupResult {
        for (level, layer) in self.layers.iter().rev().enumerate() {
            if let Some((idx, entry)) = layer.get(name.name) {
                return LookupResult { name, idx: idx as u32, level: level as u32, entry };
            }
        }
        span_bug!(name.span(), "no entry found for key: `{:?}`", name);
    }
}

impl Env<'_, '_> {
    fn conv_expr(&self, expr: &fhir::Expr) -> rty::Expr {
        match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
            fhir::ExprKind::Var(var) => self.lookup(*var).to_expr(),
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
            fhir::ExprKind::Dot(var, fld) => self.lookup(*var).get_field(self.early_cx, *fld),
        }
    }

    fn conv_func(&self, func: &fhir::Func) -> rty::Expr {
        match func {
            fhir::Func::Var(ident) => self.lookup(*ident).to_expr(),
            fhir::Func::Uif(sym, _) => rty::Expr::func(*sym),
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
        rty::Invariant { pred: Binder::new(self.conv_expr(invariant), rty::Sort::tuple(sorts)) }
    }
}

impl Layer {
    fn new<'a>(
        early_cx: &EarlyCtxt,
        iter: impl IntoIterator<Item = (&'a fhir::Name, &'a fhir::Sort)>,
    ) -> Self {
        let map = iter
            .into_iter()
            .map(|(name, sort)| {
                let conv = conv_sort(early_cx, sort);
                (*name, LayerEntry { sort: sort.clone(), conv })
            })
            .collect();
        Self { map }
    }

    fn empty() -> Self {
        Self { map: FxIndexMap::default() }
    }

    fn get(&self, name: impl Borrow<fhir::Name>) -> Option<(usize, &LayerEntry)> {
        let (idx, _, entry) = self.map.get_full(name.borrow())?;
        Some((idx, entry))
    }

    fn into_sorts(self) -> Vec<fhir::Sort> {
        self.map.into_values().map(|entry| entry.conv).collect()
    }

    fn to_sorts(&self) -> Vec<fhir::Sort> {
        self.map.values().map(|entry| entry.conv.clone()).collect()
    }
}

impl LookupResult<'_> {
    fn to_expr(&self) -> rty::Expr {
        rty::Expr::tuple_proj(rty::Expr::bvar(DebruijnIndex::new(self.level)), self.idx)
        // fn go(sort: &rty::Sort, debruijn: DebruijnIndex) -> rty::Expr {
        //     if let fhir::Sort::Tuple(sorts) = sort {
        //         rty::Expr::tuple(
        //             sorts
        //                 .iter()
        //                 .enumerate()
        //                 .map(|(i, sort)| rty::Expr::tuple_proj(go(sort, debruijn), i as u32))
        //                 .collect_vec(),
        //         )
        //     } else {
        //         rty::Expr::bvar(debruijn)
        //     }
        // }
        // go(&self.entry.conv, DebruijnIndex::new(self.level))
    }

    fn to_path(&self) -> rty::Path {
        self.to_expr().to_path().unwrap_or_else(|| {
            span_bug!(self.name.span(), "expected path, found `{:?}`", self.to_expr())
        })
    }

    fn get_field(&self, early_cx: &EarlyCtxt, fld: SurfaceIdent) -> rty::Expr {
        if let fhir::Sort::Aggregate(def_id) = &self.entry.sort {
            let i = early_cx
                .field_index(*def_id, fld.name)
                .unwrap_or_else(|| span_bug!(fld.span, "field not found `{fld:?}`"));
            rty::Expr::tuple_proj(self.to_expr(), i as u32)
        } else {
            span_bug!(fld.span, "expected aggregate sort, got `{:?}`", self.entry.sort)
        }
    }
}

pub fn conv_uif(early_cx: &EarlyCtxt, uif: &fhir::UifDef) -> rty::UifDef {
    rty::UifDef { name: uif.name, sort: conv_func_sort(early_cx, &uif.sort) }
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
        fhir::Sort::Tuple(sorts) => rty::Sort::tuple(conv_sorts(early_cx, sorts)),
        fhir::Sort::Func(fsort) => rty::Sort::Func(conv_func_sort(early_cx, fsort)),
        fhir::Sort::Aggregate(def_id) => {
            rty::Sort::tuple(conv_sorts(early_cx, early_cx.index_sorts_of(*def_id)))
        }
        fhir::Sort::Int
        | fhir::Sort::Real
        | fhir::Sort::Bool
        | fhir::Sort::Loc
        | fhir::Sort::User(_)
        | fhir::Sort::Infer => sort.clone(),
    }
}

fn conv_func_sort(early_cx: &EarlyCtxt, fsort: &fhir::FuncSort) -> rty::FuncSort {
    rty::FuncSort {
        inputs_and_output: List::from_vec(conv_sorts(early_cx, fsort.inputs_and_output.iter())),
    }
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(r),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}
