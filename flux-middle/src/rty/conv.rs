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

use flux_common::{bug, span_bug};
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    PrimTy,
};
use rustc_middle::ty::TyCtxt;

use super::{Binder, PolyVariant};
use crate::{
    early_ctxt::EarlyCtxt,
    fhir::{self, SurfaceIdent},
    global_env::GlobalEnv,
    intern::List,
    rty::{self, fold::TypeFoldable, DebruijnIndex},
    rustc::{self, ty::GenericParamDefKind},
};

pub struct ConvCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    env: Env<'a, 'tcx>,
}

struct Env<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    layers: Vec<Layer>,
}

#[derive(Debug)]
enum Layer {
    List(FxIndexMap<fhir::Name, ListEntry>),
    Single(fhir::Name, fhir::Sort, rty::Sort),
}

#[derive(Debug)]
enum ListEntry {
    Sort { sort: fhir::Sort, infer_mode: rty::InferMode, conv: rty::Sort, idx: u32 },
    Unit,
}

#[derive(Debug)]
struct LookupResult<'a> {
    name: fhir::Ident,
    level: u32,
    kind: LookupResultKind<'a>,
}

#[derive(Debug)]
enum LookupResultKind<'a> {
    List(&'a ListEntry),
    Single(&'a fhir::Sort, &'a rty::Sort),
}

pub(crate) fn expand_type_alias(genv: &GlobalEnv, alias: &fhir::TyAlias) -> rty::Binder<rty::Ty> {
    let layer = Layer::from_params(genv.early_cx(), &alias.params);
    let mut cx = ConvCtxt::new(genv, Env::with_layer(genv.early_cx(), layer));
    let ty = cx.conv_ty(&alias.ty);
    let sort = cx.env.pop_layer().into_sort();
    rty::Binder::new(ty, sort)
}

pub(crate) fn adt_def_for_struct(
    early_cx: &EarlyCtxt,
    struct_def: &fhir::StructDef,
) -> rty::AdtDef {
    let env = Env::with_layer(early_cx, Layer::from_params(early_cx, &struct_def.params));
    let sort = env.top_layer().to_sort();
    let invariants = env.conv_invariants(&sort, &struct_def.invariants);

    rty::AdtDef::new(
        early_cx.tcx.adt_def(struct_def.def_id),
        sort,
        invariants,
        struct_def.is_opaque(),
    )
}

pub(crate) fn adt_def_for_enum(early_cx: &EarlyCtxt, enum_def: &fhir::EnumDef) -> rty::AdtDef {
    let env = Env::with_layer(early_cx, Layer::from_params(early_cx, &enum_def.params));
    let sort = env.top_layer().to_sort();
    let invariants = env.conv_invariants(&sort, &enum_def.invariants);
    rty::AdtDef::new(early_cx.tcx.adt_def(enum_def.def_id), sort, invariants, false)
}

pub(crate) fn conv_defn(early_cx: &EarlyCtxt, defn: &fhir::Defn) -> rty::Defn {
    let mut env = Env::with_layer(early_cx, Layer::from_params(early_cx, &defn.args));
    let expr = env.conv_expr(&defn.expr);
    let expr = Binder::new(expr, env.pop_layer().into_sort());
    rty::Defn { name: defn.name, expr }
}

pub fn conv_qualifier(early_cx: &EarlyCtxt, qualifier: &fhir::Qualifier) -> rty::Qualifier {
    let mut env = Env::with_layer(early_cx, Layer::from_params(early_cx, &qualifier.args));
    let body = env.conv_expr(&qualifier.expr);
    let body = Binder::new(body, env.pop_layer().into_sort());
    rty::Qualifier { name: qualifier.name.clone(), body, global: qualifier.global }
}

pub(crate) fn conv_fn_sig(genv: &GlobalEnv, fn_sig: &fhir::FnSig) -> rty::PolySig {
    let layer = Layer::from_fun_params(genv.early_cx(), &fn_sig.params);
    let mut cx = ConvCtxt::new(genv, Env::with_layer(genv.early_cx(), layer));

    let mut requires = vec![];
    for constr in &fn_sig.requires {
        requires.push(cx.conv_constr(constr));
    }

    let mut args = vec![];
    for ty in &fn_sig.args {
        args.push(cx.conv_ty(ty));
    }

    let output = cx.conv_fn_output(&fn_sig.output);

    let params = cx.env.pop_layer().into_fun_params();
    rty::PolySig::new(params, rty::FnSig::new(requires, args, output))
}

impl<'a, 'tcx> ConvCtxt<'a, 'tcx> {
    fn new(genv: &'a GlobalEnv<'a, 'tcx>, env: Env<'a, 'tcx>) -> Self {
        Self { genv, env }
    }

    fn conv_fn_output(&mut self, output: &fhir::FnOutput) -> Binder<rty::FnOutput> {
        self.env
            .push_layer(Layer::from_fun_params(self.early_cx(), &output.params));

        let ret = self.conv_ty(&output.ret);
        let ensures = output
            .ensures
            .iter()
            .map(|constr| self.conv_constr(constr))
            .collect_vec();
        let output = rty::FnOutput::new(ret, ensures);

        let sort = self.env.pop_layer().into_sort();

        Binder::new(output, sort)
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
        let layer = Layer::from_fun_params(genv.early_cx(), &variant.params);
        let mut cx = ConvCtxt::new(genv, Env::with_layer(genv.early_cx(), layer));

        let fields = variant.fields.iter().map(|ty| cx.conv_ty(ty)).collect_vec();
        let args = rty::Index::from(cx.conv_refine_arg(&variant.ret.idx, &variant.ret.bty.sort()));
        let ret = cx.conv_base_ty(&variant.ret.bty, args);
        let variant = rty::VariantDef::new(fields, ret);

        let sort = cx.env.pop_layer().to_sort();
        Binder::new(variant, sort)
    }

    pub(crate) fn conv_struct_def_variant(
        genv: &GlobalEnv,
        struct_def: &fhir::StructDef,
    ) -> rty::Opaqueness<rty::PolyVariant> {
        let layer = Layer::from_params(genv.early_cx(), &struct_def.params);
        let mut cx = ConvCtxt::new(genv, Env::with_layer(genv.early_cx(), layer));

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
                            let param_ty = rty::ParamTy { index: param.index, name: param.name };
                            let bty = rty::BaseTy::Param(param_ty);
                            let ty = rty::Ty::indexed(bty, rty::Expr::nu());
                            rty::GenericArg::BaseTy(Binder::new(ty, rty::Sort::Param(param_ty)))
                        }
                        GenericParamDefKind::Lifetime => rty::GenericArg::Lifetime,
                    }
                })
                .collect_vec();

            let sort = cx.env.pop_layer().to_sort();
            let ret = rty::Ty::indexed(
                rty::BaseTy::adt(genv.adt_def(def_id), substs),
                rty::Expr::nu().eta_expand_tuple(&sort),
            );
            let variant = rty::VariantDef::new(fields, ret);
            rty::Opaqueness::Transparent(Binder::new(variant, sort))
        } else {
            rty::Opaqueness::Opaque
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
                    let idx = rty::Index::from(rty::Expr::unit());
                    self.conv_base_ty(bty, idx)
                } else {
                    self.env.push_layer(Layer::empty());
                    let idx = rty::Index::from(rty::Expr::nu());
                    let ty = self.conv_base_ty(bty, idx);
                    self.env.pop_layer();
                    rty::Ty::exists(Binder::new(ty, sort))
                }
            }
            fhir::Ty::Indexed(bty, idx) => {
                let idxs = rty::Index::from(self.conv_refine_arg(idx, &bty.sort()));
                self.conv_base_ty(bty, idxs)
            }
            fhir::Ty::Exists(bty, bind, pred) => {
                let layer = Layer::single(self.early_cx(), *bind, bty.sort());

                self.env.push_layer(layer);
                let idx = rty::Index::from(self.env.lookup(*bind).to_expr());
                let ty = self.conv_base_ty(bty, idx);
                let pred = self.env.conv_expr(pred);
                let constr = rty::Ty::constr(pred, ty);
                let sort = self.env.pop_layer().into_sort();

                if sort.is_unit() {
                    constr.shift_out_bvars(1)
                } else {
                    rty::Ty::exists(Binder::new(constr, sort))
                }
            }
            fhir::Ty::Ptr(loc) => rty::Ty::ptr(rty::RefKind::Mut, self.env.lookup(*loc).to_path()),
            fhir::Ty::Ref(rk, ty) => rty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(ty)),
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
        let (expr, is_binder) = match arg {
            fhir::RefineArg::Expr {
                expr: fhir::Expr { kind: fhir::ExprKind::Var(var), .. },
                is_binder,
            } => (self.env.lookup(*var).to_expr(), rty::TupleTree::Leaf(*is_binder)),
            fhir::RefineArg::Expr { expr, is_binder } => {
                (self.env.conv_expr(expr), rty::TupleTree::Leaf(*is_binder))
            }
            fhir::RefineArg::Abs(params, body, _) => {
                let fsort = self.expect_func(sort);
                let params = iter::zip(params, fsort.inputs())
                    .map(|((name, _), sort)| (*name, sort.clone()))
                    .collect_vec();
                let layer = Layer::from_params(self.early_cx(), &params);

                self.env.push_layer(layer);
                let pred = self.env.conv_expr(body);
                let sort = self.env.pop_layer().to_sort();

                let body = rty::Binder::new(pred, sort);
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
        };
        (self.coerce_index(expr, sort), is_binder)
    }

    fn coerce_index(&self, mut expr: rty::Expr, sort: &fhir::Sort) -> rty::Expr {
        if self.early_cx().is_single_field_adt(sort).is_some() && !expr.is_tuple() {
            expr = rty::Expr::tuple(vec![expr]);
        } else if !matches!(sort, fhir::Sort::Aggregate(_) | fhir::Sort::Unit) && expr.is_tuple() {
            expr = rty::Expr::tuple_proj(expr, 0);
        }
        expr
    }

    fn conv_ref_kind(rk: fhir::RefKind) -> rty::RefKind {
        match rk {
            fhir::RefKind::Mut => rty::RefKind::Mut,
            fhir::RefKind::Shr => rty::RefKind::Shr,
        }
    }

    fn conv_base_ty(&mut self, bty: &fhir::BaseTy, idx: rty::Index) -> rty::Ty {
        match bty {
            fhir::BaseTy::Path(path, args) => self.conv_path(path, args, idx),
            fhir::BaseTy::Slice(ty) => {
                let slice = rty::BaseTy::slice(self.conv_ty(ty));
                rty::Ty::indexed(slice, idx)
            }
        }
    }

    fn conv_path(
        &mut self,
        path: &fhir::Path,
        early: &[fhir::RefineArg],
        idx: rty::Index,
    ) -> rty::Ty {
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
            fhir::Res::Adt(did) => {
                let adt_def = self.genv.adt_def(*did);
                let substs = self.conv_generic_args(*did, &path.generics, adt_def.is_box());
                rty::BaseTy::adt(adt_def, substs)
            }
            fhir::Res::Param(def_id) => {
                rty::BaseTy::Param(def_id_to_param_ty(self.genv.tcx, def_id.expect_local()))
            }
            fhir::Res::Alias(def_id) => {
                let mut args = vec![];
                for (arg, sort) in iter::zip(early, self.genv.early_bound_sorts_of(*def_id)) {
                    let (expr, _) = self.conv_refine_arg(arg, sort);
                    args.push(expr);
                }
                let index_sorts = conv_sorts(self.early_cx(), self.genv.index_sorts_of(*def_id));
                args.extend(
                    idx.expr
                        .eta_expand_tuple(&rty::Sort::tuple(index_sorts))
                        .expect_tuple()
                        .iter()
                        .cloned(),
                );

                return self
                    .genv
                    .type_of(*def_id)
                    .replace_generics(&self.conv_generic_args(*def_id, &path.generics, false))
                    .replace_bvar(&rty::Expr::tuple(args));
            }
        };
        rty::Ty::indexed(bty, idx)
    }

    fn conv_generic_args(
        &mut self,
        def_id: DefId,
        args: &[fhir::Ty],
        is_box: bool,
    ) -> Vec<rty::GenericArg> {
        let mut i = 0;
        let kind = if is_box { rty::TyVarKind::Type } else { rty::TyVarKind::BaseTy };
        self.genv
            .generics_of(def_id)
            .params
            .iter()
            .map(|generic| {
                match &generic.kind {
                    GenericParamDefKind::Type { has_default } => {
                        if i < args.len() {
                            i += 1;
                            self.conv_generic_arg(&args[i - 1], kind)
                        } else {
                            debug_assert!(has_default);
                            let arg =
                                rustc::ty::GenericArg::Ty(self.genv.lower_type_of(generic.def_id));
                            self.genv.refine_generic_arg(&arg, rty::Expr::tt, kind)
                        }
                    }
                    GenericParamDefKind::Lifetime => rty::GenericArg::Lifetime,
                }
            })
            .collect()
    }

    fn conv_generic_arg(&mut self, arg: &fhir::Ty, kind: rty::TyVarKind) -> rty::GenericArg {
        let ty = self.conv_ty(arg);
        if matches!(kind, rty::TyVarKind::Type) {
            return rty::GenericArg::Ty(ty);
        }
        match ty.kind() {
            rty::TyKind::Indexed(bty, idx) => {
                let bty = bty.shift_in_bvars(1);
                let sort = bty.sort();
                let pred = rty::Expr::eq(rty::Expr::nu(), &idx.expr.shift_in_bvars(1));
                let ty = if pred.is_trivially_true() {
                    rty::Ty::indexed(bty, rty::Expr::nu())
                } else {
                    rty::Ty::constr(pred, rty::Ty::indexed(bty, rty::Expr::nu()))
                };
                rty::GenericArg::BaseTy(rty::Binder::new(ty, sort))
            }
            rty::TyKind::Exists(ty) => rty::GenericArg::BaseTy(ty.clone()),
            rty::TyKind::Constr(..) => {
                todo!()
            }
            rty::TyKind::Uninit | rty::TyKind::Ptr(_, _) | rty::TyKind::Discr(_, _) => {
                bug!()
            }
        }
    }

    fn early_cx(&self) -> &EarlyCtxt<'a, 'tcx> {
        self.genv.early_cx()
    }

    fn expect_func(&self, sort: &fhir::Sort) -> fhir::FuncSort {
        self.early_cx().is_coercible_to_func(sort).unwrap()
    }
}

impl<'a, 'tcx> Env<'a, 'tcx> {
    fn with_layer(early_cx: &'a EarlyCtxt<'a, 'tcx>, layer: Layer) -> Self {
        Self { early_cx, layers: vec![layer] }
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
            if let Some(kind) = layer.get(name.name) {
                return LookupResult { name, level: level as u32, kind };
            }
        }
        span_bug!(name.span(), "no entry found for key: `{:?}`", name);
    }
}

impl Env<'_, '_> {
    fn conv_expr(&self, expr: &fhir::Expr) -> rty::Expr {
        match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
            fhir::ExprKind::Var(var) => self.lookup(*var).to_expr().singleton_proj_coercion(),
            fhir::ExprKind::Literal(lit) => rty::Expr::constant(conv_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                rty::Expr::binary_op(*op, self.conv_expr(e1), self.conv_expr(e2))
            }
            fhir::ExprKind::UnaryOp(op, e) => rty::Expr::unary_op(*op, self.conv_expr(e)),
            fhir::ExprKind::App(func, args) => {
                rty::Expr::app(self.conv_func(func), rty::Expr::tuple(self.conv_exprs(args)))
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                rty::Expr::ite(self.conv_expr(p), self.conv_expr(e1), self.conv_expr(e2))
            }
            fhir::ExprKind::Dot(var, fld) => self.lookup(*var).get_field(self.early_cx, *fld),
        }
    }

    fn conv_func(&self, func: &fhir::Func) -> rty::Expr {
        match func {
            fhir::Func::Var(ident) => self.lookup(*ident).to_expr().singleton_proj_coercion(),
            fhir::Func::Uif(sym, _) => rty::Expr::func(*sym),
        }
    }

    fn conv_exprs(&self, exprs: &[fhir::Expr]) -> List<rty::Expr> {
        List::from_iter(exprs.iter().map(|e| self.conv_expr(e)))
    }

    fn conv_invariants(&self, sort: &rty::Sort, invariants: &[fhir::Expr]) -> Vec<rty::Invariant> {
        invariants
            .iter()
            .map(|invariant| self.conv_invariant(sort, invariant))
            .collect()
    }

    fn conv_invariant(&self, sort: &rty::Sort, invariant: &fhir::Expr) -> rty::Invariant {
        rty::Invariant { pred: Binder::new(self.conv_expr(invariant), sort.clone()) }
    }
}

impl Layer {
    fn from_params<'a>(
        early_cx: &EarlyCtxt,
        slice: impl IntoIterator<Item = &'a (fhir::Ident, fhir::Sort)>,
    ) -> Self {
        let mut idx = 0;
        let map = slice
            .into_iter()
            .map(|(ident, sort)| {
                let entry = ListEntry::new(early_cx, idx, sort.clone(), None);
                idx += 1;
                (ident.name, entry)
            })
            .collect();
        Self::List(map)
    }

    fn from_fun_params(early_cx: &EarlyCtxt, params: &[fhir::FunRefineParam]) -> Self {
        let mut idx = 0;
        let map = params
            .iter()
            .map(|param| {
                let entry = ListEntry::new(early_cx, idx, param.sort.clone(), Some(param.mode));
                idx += !matches!(entry, ListEntry::Unit) as u32;
                (param.name.name, entry)
            })
            .collect();
        Self::List(map)
    }

    fn single(early_cx: &EarlyCtxt, bind: fhir::Ident, sort: fhir::Sort) -> Self {
        let conv = conv_sort(early_cx, &sort);
        Self::Single(bind.name, sort, conv)
    }

    fn empty() -> Self {
        Self::List(FxIndexMap::default())
    }

    fn get(&self, name: impl Borrow<fhir::Name>) -> Option<LookupResultKind> {
        match self {
            Layer::List(map) => Some(LookupResultKind::List(map.get(name.borrow())?)),
            Layer::Single(bname, sort, conv) => {
                if bname == name.borrow() {
                    Some(LookupResultKind::Single(sort, conv))
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

impl LookupResultKind<'_> {
    fn to_expr(&self, level: u32) -> rty::Expr {
        match self {
            Self::List(ListEntry::Sort { idx, conv, .. }) => {
                rty::Expr::tuple_proj(rty::Expr::bvar(DebruijnIndex::new(level)), *idx)
                    .eta_expand_tuple(conv)
            }
            Self::List(ListEntry::Unit) => rty::Expr::unit(),
            Self::Single(_, conv) => {
                rty::Expr::bvar(DebruijnIndex::new(level)).eta_expand_tuple(conv)
            }
        }
    }

    fn is_aggregate(&self) -> Option<DefId> {
        match self {
            Self::Single(fhir::Sort::Aggregate(def_id), _) => Some(*def_id),
            Self::List(ListEntry::Sort { sort: fhir::Sort::Aggregate(def_id), .. }) => {
                Some(*def_id)
            }
            _ => None,
        }
    }
}

impl LookupResult<'_> {
    fn to_expr(&self) -> rty::Expr {
        self.kind.to_expr(self.level)
    }

    fn to_path(&self) -> rty::Path {
        self.to_expr().to_path().unwrap_or_else(|| {
            span_bug!(self.name.span(), "expected path, found `{:?}`", self.to_expr())
        })
    }

    fn get_field(&self, early_cx: &EarlyCtxt, fld: SurfaceIdent) -> rty::Expr {
        if let Some(def_id) = self.kind.is_aggregate() {
            let i = early_cx
                .field_index(def_id, fld.name)
                .unwrap_or_else(|| span_bug!(fld.span, "field not found `{fld:?}`"));
            rty::Expr::tuple_proj(self.to_expr(), i as u32)
        } else {
            span_bug!(fld.span, "expected aggregate sort")
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
        fhir::Sort::Int => rty::Sort::Int,
        fhir::Sort::Real => rty::Sort::Real,
        fhir::Sort::Bool => rty::Sort::Bool,
        fhir::Sort::Loc => rty::Sort::Loc,
        fhir::Sort::Unit => rty::Sort::unit(),
        fhir::Sort::User(name) => rty::Sort::User(*name),
        fhir::Sort::Func(fsort) => rty::Sort::Func(conv_func_sort(early_cx, fsort)),
        fhir::Sort::Aggregate(def_id) => {
            rty::Sort::tuple(conv_sorts(early_cx, early_cx.index_sorts_of(*def_id)))
        }
        fhir::Sort::Param(def_id) => {
            rty::Sort::Param(def_id_to_param_ty(early_cx.tcx, def_id.expect_local()))
        }
        fhir::Sort::Infer => bug!("unexpected sort `Infer`"),
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
