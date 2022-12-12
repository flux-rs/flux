//! Conversion types in [`crate::fhir`] to types in [`crate::rty`]
//!
//! Conversion assumes well-formedness and will panic if they are not.  Well-formedness implies
//! among other things:
//! 1. Names are bound correctly
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`crate::rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted
use std::iter;

use flux_common::index::IndexGen;
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
    name_map: NameMap,
}

#[derive(Default, Debug)]
struct NameMap {
    map: FxHashMap<fhir::Name, Entry>,
}

#[derive(Copy, Clone, Debug)]
enum Entry {
    Bound { level: u32, index: usize },
    Free(rty::Name),
}

impl From<rty::Name> for Entry {
    fn from(v: rty::Name) -> Self {
        Self::Free(v)
    }
}

pub(crate) fn conv_adt_def(tcx: TyCtxt, adt_def: &fhir::AdtDef) -> rty::AdtDef {
    let mut name_map = NameMap::default();
    let sorts = name_map.conv_refined_by(&adt_def.refined_by);

    let invariants = adt_def
        .invariants
        .iter()
        .map(|invariant| name_map.conv_invariant(&sorts, invariant))
        .collect_vec();

    rty::AdtDef::new(tcx.adt_def(adt_def.def_id), sorts, invariants, adt_def.opaque)
}

pub(crate) fn conv_defn(defn: &fhir::Defn) -> rty::Defn {
    let name_map = NameMap::with_bvars(defn.args.iter().map(|(ident, _)| ident.name));
    let sorts = defn.args.iter().map(|(_, sort)| sort.clone()).collect_vec();
    let expr = Binders::new(name_map.conv_expr(&defn.expr, 1), sorts);
    rty::Defn { name: defn.name, expr }
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    fn from_refined_by(genv: &'a GlobalEnv<'genv, 'tcx>, refined_by: &fhir::RefinedBy) -> Self {
        let name_map = NameMap::with_bvars(refined_by.params.iter().map(|(ident, _)| ident.name));
        Self { genv, name_map }
    }

    fn from_params(genv: &'a GlobalEnv<'genv, 'tcx>, params: &[fhir::RefineParam]) -> Self {
        let name_map = NameMap::with_bvars(params.iter().map(|param| param.name.name));
        Self { genv, name_map }
    }

    pub(crate) fn conv_fn_sig(genv: &GlobalEnv, fn_sig: &fhir::FnSig) -> rty::PolySig {
        let mut cx = ConvCtxt::from_params(genv, &fn_sig.params);

        let mut requires = vec![];
        for constr in &fn_sig.requires {
            requires.push(cx.conv_constr(constr, 1));
        }

        let mut args = vec![];
        for ty in &fn_sig.args {
            args.push(cx.conv_ty(ty, 1));
        }

        let mut ensures = vec![];
        for constr in &fn_sig.ensures {
            ensures.push(cx.conv_constr(constr, 1));
        }

        let ret = cx.conv_ty(&fn_sig.ret, 1);

        let sorts = fn_sig
            .params
            .iter()
            .map(|param| param.sort.clone())
            .collect_vec();
        rty::PolySig::new(rty::Binders::new(rty::FnSig::new(requires, args, ret, ensures), sorts))
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
        let fields = variant
            .fields
            .iter()
            .map(|ty| cx.conv_ty(ty, 1))
            .collect_vec();
        let sorts = variant
            .params
            .iter()
            .map(|param| param.sort.clone())
            .collect_vec();
        let variant = rty::VariantDef::new(fields, cx.conv_variant_ret(&variant.ret));
        Binders::new(variant, sorts)
    }

    fn conv_variant_ret(&mut self, ret: &fhir::VariantRet) -> VariantRet {
        let bty = self.conv_base_ty(&ret.bty, 1);
        let args = List::from_iter(
            iter::zip(&ret.indices.indices, bty.sorts())
                .map(|(arg, sort)| self.conv_arg(arg, sort, 1)),
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
                        Some(ty) => cx.conv_ty(ty, 1),
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

            let sorts = refined_by.sorts().cloned().collect_vec();
            let idxs = sorts
                .iter()
                .enumerate()
                .map(|(idx, _)| rty::Expr::bvar(rty::BoundVar::innermost(idx)).into());
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

    fn conv_constr(&mut self, constr: &fhir::Constraint, nbinders: u32) -> rty::Constraint {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                rty::Constraint::Type(
                    self.name_map.get(loc.name, nbinders).to_path(),
                    self.conv_ty(ty, nbinders),
                )
            }
            fhir::Constraint::Pred(pred) => rty::Constraint::Pred(self.name_map.conv_pred(pred, 1)),
        }
    }

    pub fn conv_qualifier(qualifier: &fhir::Qualifier) -> rty::Qualifier {
        let mut name_map = NameMap::default();
        let name_gen = IndexGen::new();

        let args = qualifier
            .args
            .iter()
            .map(|(ident, sort)| {
                let fresh = name_gen.fresh();
                name_map.insert(ident.name, fresh);
                (fresh, sort.clone())
            })
            .collect_vec();

        let expr = name_map.conv_expr(&qualifier.expr, 1);

        rty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    fn conv_ty(&mut self, ty: &fhir::Ty, nbinders: u32) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                let bty = self.conv_base_ty(bty, nbinders);
                let sorts = bty.sorts();
                if sorts.is_empty() {
                    rty::Ty::indexed(bty, rty::RefineArgs::empty())
                } else {
                    let pred = rty::Binders::new(rty::Pred::tt(), sorts);
                    rty::Ty::exists(bty, pred)
                }
            }
            fhir::Ty::Indexed(bty, idxs) => {
                let bty = self.conv_base_ty(bty, nbinders);
                let idxs = self.conv_indices(idxs, bty.sorts(), nbinders);
                rty::Ty::indexed(bty, idxs)
            }
            fhir::Ty::Exists(bty, binders, pred) => {
                let bty = self.conv_base_ty(bty, nbinders);
                self.name_map
                    .with_binders(binders, nbinders, |name_map, nbinders| {
                        let pred = name_map.conv_pred(pred, nbinders);
                        let pred = rty::Binders::new(pred, bty.sorts());
                        rty::Ty::exists(bty, pred)
                    })
            }
            fhir::Ty::Ptr(loc) => {
                rty::Ty::ptr(rty::RefKind::Mut, self.name_map.get(loc.name, nbinders).to_path())
            }
            fhir::Ty::Ref(rk, ty) => {
                rty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(ty, nbinders))
            }
            fhir::Ty::Param(param) => rty::Ty::param(*param),
            fhir::Ty::Float(float_ty) => rty::Ty::float(*float_ty),
            fhir::Ty::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.conv_ty(ty, nbinders))
                    .collect_vec();
                rty::Ty::tuple(tys)
            }
            fhir::Ty::Never => rty::Ty::never(),
            fhir::Ty::Constr(pred, ty) => {
                let pred = self.name_map.conv_pred(pred, nbinders);
                rty::Ty::constr(pred, self.conv_ty(ty, nbinders))
            }
            fhir::Ty::Array(ty, _) => rty::Ty::array(self.conv_ty(ty, nbinders), rty::Const),
            fhir::Ty::Slice(ty) => rty::Ty::slice(self.conv_ty(ty, nbinders)),
            fhir::Ty::Str => rty::Ty::str(),
            fhir::Ty::Char => rty::Ty::char(),
        }
    }

    fn conv_indices(
        &mut self,
        idxs: &fhir::Indices,
        sorts: &[fhir::Sort],
        nbinders: u32,
    ) -> rty::RefineArgs {
        rty::RefineArgs::new(iter::zip(&idxs.indices, sorts).map(|(arg, sort)| {
            let is_binder = matches!(arg, fhir::RefineArg::Expr { is_binder: true, .. });
            (self.conv_arg(arg, sort, nbinders), is_binder)
        }))
    }

    fn conv_arg(
        &mut self,
        arg: &fhir::RefineArg,
        sort: &fhir::Sort,
        nbinders: u32,
    ) -> rty::RefineArg {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => {
                rty::RefineArg::Expr(self.name_map.conv_expr(expr, nbinders))
            }
            fhir::RefineArg::Abs(params, body, _) => {
                let fsort = sort.as_func();
                let abs = self
                    .name_map
                    .with_binders(params, nbinders, |name_map, nbinders| {
                        let pred = name_map.conv_pred(body, nbinders);
                        rty::Binders::new(pred, fsort.inputs())
                    });
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

    fn conv_base_ty(&mut self, bty: &fhir::BaseTy, nbinders: u32) -> rty::BaseTy {
        match bty {
            fhir::BaseTy::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            fhir::BaseTy::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            fhir::BaseTy::Bool => rty::BaseTy::Bool,
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
                                        self.conv_generic_arg(&substs[i - 1], nbinders)
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

    fn conv_generic_arg(&mut self, arg: &fhir::Ty, nbinders: u32) -> rty::GenericArg {
        rty::GenericArg::Ty(self.conv_ty(arg, nbinders))
    }
}

impl NameMap {
    fn with_bvars(iter: impl IntoIterator<Item = fhir::Name>) -> Self {
        Self {
            map: iter
                .into_iter()
                .enumerate()
                .map(|(index, name)| (name, Entry::Bound { index, level: 0 }))
                .collect(),
        }
    }

    fn insert(&mut self, name: fhir::Name, var: impl Into<Entry>) {
        self.map.insert(name, var.into());
    }

    fn get(&self, name: fhir::Name, nbinders: u32) -> rty::Var {
        match self.map[&name] {
            Entry::Bound { level, index } => {
                rty::Var::Bound(rty::BoundVar::new(index, DebruijnIndex::new(nbinders - level - 1)))
            }
            Entry::Free(name) => rty::Var::Free(name),
        }
    }

    fn with_binders<R>(
        &mut self,
        binders: &[fhir::Name],
        nbinders: u32,
        f: impl FnOnce(&mut Self, u32) -> R,
    ) -> R {
        for (index, binder) in binders.iter().enumerate() {
            self.insert(*binder, Entry::Bound { index, level: nbinders });
        }
        let r = f(self, nbinders + 1);
        for binder in binders {
            self.map.remove(binder);
        }
        r
    }

    fn conv_invariant(&self, sorts: &[rty::Sort], invariant: &fhir::Expr) -> rty::Invariant {
        rty::Invariant { pred: Binders::new(self.conv_expr(invariant, 1), sorts) }
    }

    fn conv_refined_by(&mut self, refined_by: &fhir::RefinedBy) -> Vec<rty::Sort> {
        refined_by
            .params
            .iter()
            .enumerate()
            .map(|(index, (ident, sort))| {
                self.map
                    .insert(ident.name, Entry::Bound { index, level: 0 });
                sort.clone()
            })
            .collect()
    }

    fn conv_pred(&self, expr: &fhir::Expr, nbinders: u32) -> rty::Pred {
        fn go(this: &NameMap, expr: &fhir::Expr, nbinders: u32, preds: &mut Vec<rty::Pred>) {
            match &expr.kind {
                fhir::ExprKind::BinaryOp(fhir::BinOp::And, box [e1, e2]) => {
                    go(this, e1, nbinders, preds);
                    go(this, e2, nbinders, preds);
                }
                fhir::ExprKind::App(fhir::Func::Var(func), args) => {
                    let func = this.get(func.name, nbinders);
                    let args = this.conv_exprs(args, nbinders);
                    preds.push(rty::Pred::App(func, args));
                }
                _ => {
                    preds.push(rty::Pred::Expr(this.conv_expr(expr, nbinders)));
                }
            }
        }
        let mut preds = vec![];
        go(self, expr, nbinders, &mut preds);

        rty::Pred::And(List::from_vec(preds))
    }

    fn conv_expr(&self, expr: &fhir::Expr, nbinders: u32) -> rty::Expr {
        match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
            fhir::ExprKind::Var(name, ..) => self.get(*name, nbinders).to_expr(),
            fhir::ExprKind::Literal(lit) => rty::Expr::constant(conv_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                rty::Expr::binary_op(
                    *op,
                    self.conv_expr(e1, nbinders),
                    self.conv_expr(e2, nbinders),
                )
            }
            fhir::ExprKind::App(func, args) => {
                match func {
                    fhir::Func::Uif(sym, _) => {
                        rty::Expr::app(*sym, self.conv_exprs(args, nbinders))
                    }
                    fhir::Func::Var(..) => unreachable!("refinement variable in wrong position"),
                }
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                rty::Expr::ite(
                    self.conv_expr(p, nbinders),
                    self.conv_expr(e1, nbinders),
                    self.conv_expr(e2, nbinders),
                )
            }
        }
    }

    fn conv_exprs(&self, exprs: &[fhir::Expr], nbinders: u32) -> List<rty::Expr> {
        List::from_iter(exprs.iter().map(|e| self.conv_expr(e, nbinders)))
    }
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}
