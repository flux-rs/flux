//! Conversion from desugared types in [`crate::fhir`] to types in [`crate::rty`]
use std::iter;

use flux_common::index::IndexGen;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_target::abi::VariantIdx;

use super::{Binders, PolyVariant, VariantRet};
use crate::{
    fhir::{self, AdtDef},
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

impl NameMap {
    fn insert(&mut self, name: fhir::Name, var: impl Into<Entry>) {
        self.map.insert(name, var.into());
    }

    fn get(&self, name: fhir::Name, nbinders: u32) -> rty::Expr {
        match self.map[&name] {
            Entry::Bound { level, index } => {
                rty::Expr::bvar(rty::BoundVar::new(index, DebruijnIndex::new(nbinders - level - 1)))
            }
            Entry::Free(name) => rty::Expr::fvar(name),
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
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    pub(crate) fn new(genv: &'a GlobalEnv<'genv, 'tcx>) -> Self {
        Self { genv, name_map: NameMap::default() }
    }

    pub(crate) fn conv_fn_sig(genv: &GlobalEnv, fn_sig: fhir::FnSig) -> rty::Binders<rty::FnSig> {
        let mut cx = ConvCtxt::new(genv);

        let params = cx.conv_params(&fn_sig.params);

        let mut requires = vec![];
        for constr in fn_sig.requires {
            requires.push(cx.conv_constr(&constr, 1));
        }

        let mut args = vec![];
        for ty in fn_sig.args {
            args.push(cx.conv_ty(&ty, 1));
        }

        let mut ensures = vec![];
        for constr in fn_sig.ensures {
            ensures.push(cx.conv_constr(&constr, 1));
        }

        let ret = cx.conv_ty(&fn_sig.ret, 1);

        rty::Binders::new(rty::FnSig::new(requires, args, ret, ensures), params)
    }

    pub(crate) fn conv_adt_def(genv: &GlobalEnv, adt: &fhir::AdtDef) -> rty::AdtDef {
        let mut cx = ConvCtxt::new(genv);
        let sorts = cx.conv_params(&adt.refined_by);
        let invariants = adt
            .invariants
            .iter()
            .map(|invariant| cx.conv_invariant(&sorts, invariant))
            .collect_vec();

        rty::AdtDef::new(genv.tcx.adt_def(adt.def_id), sorts, invariants, adt.opaque)
    }

    pub(crate) fn conv_enum_def_variants(
        genv: &mut GlobalEnv,
        enum_def: fhir::EnumDef,
    ) -> Option<Vec<PolyVariant>> {
        let mut cx = ConvCtxt::new(genv);
        let variants: Vec<PolyVariant> = enum_def
            .variants
            .into_iter()
            .map(|variant| cx.conv_variant(variant))
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

    fn conv_variant(&mut self, variant: fhir::VariantDef) -> PolyVariant {
        let sorts = self.conv_params(&variant.params);
        let fields = variant
            .fields
            .iter()
            .map(|ty| self.conv_ty(ty, 1))
            .collect_vec();
        let variant = rty::VariantDef::new(fields, self.conv_variant_ret(variant.ret));
        Binders::new(variant, sorts)
    }

    fn conv_variant_ret(&mut self, ret: fhir::VariantRet) -> VariantRet {
        let indices = ret
            .indices
            .indices
            .iter()
            .map(|idx| self.conv_expr(&idx.expr))
            .collect_vec();
        VariantRet { bty: self.conv_base_ty(&ret.bty, 1), indices: List::from_vec(indices) }
    }

    pub(crate) fn conv_struct_def_variant(
        genv: &GlobalEnv,
        adt_data: &AdtDef,
        struct_def: &fhir::StructDef,
    ) -> Option<rty::PolyVariant> {
        let mut cx = ConvCtxt::new(genv);
        let sorts = cx.conv_params(&adt_data.refined_by);
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

            let idxs = sorts
                .iter()
                .enumerate()
                .map(|(idx, _)| rty::Expr::bvar(rty::BoundVar::innermost(idx)))
                .collect_vec();
            let ret = VariantRet {
                bty: rty::BaseTy::adt(genv.adt_def(def_id), substs),
                indices: List::from_vec(idxs),
            };
            let variant = rty::VariantDef::new(fields, ret);
            Some(Binders::new(variant, sorts))
        } else {
            None
        }
    }

    fn conv_params(&mut self, params: &[fhir::Param]) -> Vec<rty::Sort> {
        params
            .iter()
            .enumerate()
            .map(|(index, param)| {
                self.name_map
                    .insert(param.name.name, Entry::Bound { index, level: 0 });
                conv_sort(param.sort)
            })
            .collect()
    }

    fn conv_constr(&mut self, constr: &fhir::Constraint, nbinders: u32) -> rty::Constraint {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                rty::Constraint::Type(
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                    self.conv_ty(ty, nbinders),
                )
            }
            fhir::Constraint::Pred(e) => rty::Constraint::Pred(conv_expr(e, &self.name_map, 1)),
        }
    }

    pub fn conv_qualifier(qualifier: &fhir::Qualifier) -> rty::Qualifier {
        let mut name_map = NameMap::default();
        let name_gen = IndexGen::new();

        let args = qualifier
            .args
            .iter()
            .map(|param| {
                let fresh = name_gen.fresh();
                name_map.insert(param.name.name, fresh);
                (fresh, conv_sort(param.sort))
            })
            .collect_vec();

        let expr = conv_expr(&qualifier.expr, &name_map, 1);

        rty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    fn conv_invariant(&self, sorts: &[rty::Sort], invariant: &fhir::Expr) -> rty::Invariant {
        rty::Invariant {
            pred: Binders::new(self.conv_expr(invariant), sorts),
            source_info: invariant.span.data(),
        }
    }

    fn conv_expr(&self, expr: &fhir::Expr) -> rty::Expr {
        conv_expr(expr, &self.name_map, 1)
    }

    fn conv_ty(&mut self, ty: &fhir::Ty, nbinders: u32) -> rty::Ty {
        match ty {
            fhir::Ty::BaseTy(bty) => {
                let bty = self.conv_base_ty(bty, nbinders);
                let sorts = bty.sorts();
                if sorts.is_empty() {
                    rty::Ty::indexed(bty, vec![])
                } else {
                    let pred = rty::Binders::new(rty::Pred::tt(), sorts);
                    rty::Ty::exists(bty, pred)
                }
            }
            fhir::Ty::Indexed(bty, indices) => {
                let indices = indices
                    .indices
                    .iter()
                    .map(|idx| self.conv_index(idx, nbinders))
                    .collect_vec();
                rty::Ty::indexed(self.conv_base_ty(bty, nbinders), indices)
            }
            fhir::Ty::Exists(bty, binders, pred) => {
                let bty = self.conv_base_ty(bty, nbinders);
                self.name_map
                    .with_binders(binders, nbinders, |name_map, nbinders| {
                        let expr = conv_expr(pred, name_map, nbinders);
                        let pred = rty::Binders::new(rty::Pred::Expr(expr), bty.sorts());
                        rty::Ty::exists(bty, pred)
                    })
            }
            fhir::Ty::Ptr(loc) => {
                rty::Ty::ptr(
                    rty::RefKind::Mut,
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                )
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
                let pred = conv_expr(pred, &self.name_map, nbinders);
                rty::Ty::constr(pred, self.conv_ty(ty, nbinders))
            }
            fhir::Ty::Array(ty, _) => rty::Ty::array(self.conv_ty(ty, nbinders), rty::Const),
            fhir::Ty::Slice(ty) => rty::Ty::slice(self.conv_ty(ty, nbinders)),
            fhir::Ty::Str => rty::Ty::str(),
            fhir::Ty::Char => rty::Ty::char(),
        }
    }

    fn conv_index(&self, idx: &fhir::Index, nbinders: u32) -> rty::Index {
        rty::Index {
            expr: conv_expr(&idx.expr, &self.name_map, nbinders),
            is_binder: idx.is_binder,
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
                let generics = self.genv.generics_of(*did);
                let defaults = generics.params.iter().skip(substs.len()).map(|generic| {
                    match &generic.kind {
                        GenericParamDefKind::Type { has_default } => {
                            debug_assert!(has_default);
                            rty::GenericArg::Ty(self.genv.default_type_of(generic.def_id))
                        }
                        GenericParamDefKind::Lifetime => {
                            unreachable!("missing lifetime argument during conversion")
                        }
                    }
                });
                let adt_def = self.genv.adt_def(*did);
                let substs = List::from_vec(
                    substs
                        .iter()
                        .map(|ty| self.conv_generic_arg(ty, nbinders))
                        .chain(defaults)
                        .collect(),
                );
                rty::BaseTy::adt(adt_def, substs)
            }
        }
    }

    fn conv_generic_arg(&mut self, arg: &fhir::Ty, nbinders: u32) -> rty::GenericArg {
        rty::GenericArg::Ty(self.conv_ty(arg, nbinders))
    }
}

fn conv_expr(expr: &fhir::Expr, name_map: &NameMap, nbinders: u32) -> rty::Expr {
    match &expr.kind {
        fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did),
        fhir::ExprKind::Var(name, ..) => name_map.get(*name, nbinders),
        fhir::ExprKind::Literal(lit) => rty::Expr::constant(conv_lit(*lit)),
        fhir::ExprKind::BinaryOp(op, e1, e2) => {
            rty::Expr::binary_op(
                *op,
                conv_expr(e1, name_map, nbinders),
                conv_expr(e2, name_map, nbinders),
            )
        }
        fhir::ExprKind::App(f, exprs) => {
            let exprs = exprs
                .iter()
                .map(|e| conv_expr(e, name_map, nbinders))
                .collect();
            rty::Expr::app(f.symbol, exprs)
        }
        fhir::ExprKind::IfThenElse(p, e1, e2) => {
            rty::Expr::ite(
                conv_expr(p, name_map, nbinders),
                conv_expr(e1, name_map, nbinders),
                conv_expr(e2, name_map, nbinders),
            )
        }
    }
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}

pub fn conv_sort(sort: fhir::Sort) -> rty::Sort {
    match sort {
        fhir::Sort::Int => rty::Sort::Int,
        fhir::Sort::Bool => rty::Sort::Bool,
        fhir::Sort::Loc => rty::Sort::Loc,
    }
}
