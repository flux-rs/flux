//! Conversion from desugared types in [`crate::core`] to types in [`crate::ty`]
use std::iter;

use flux_common::index::IndexGen;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_target::abi::VariantIdx;

use super::{Binders, PolyVariant};
use crate::{
    core,
    global_env::GlobalEnv,
    rustc::ty::GenericParamDefKind,
    ty::{self, DebruijnIndex},
};

pub struct ConvCtxt<'a, 'genv, 'tcx> {
    genv: &'a GlobalEnv<'genv, 'tcx>,
    name_map: NameMap,
}

#[derive(Default, Debug)]
struct NameMap {
    map: FxHashMap<core::Name, Entry>,
}

#[derive(Copy, Clone, Debug)]
enum Entry {
    Bound { level: u32, index: usize },
    Free(ty::Name),
}

impl From<ty::Name> for Entry {
    fn from(v: ty::Name) -> Self {
        Self::Free(v)
    }
}

impl NameMap {
    fn insert(&mut self, name: core::Name, var: impl Into<Entry>) {
        self.map.insert(name, var.into());
    }

    fn get(&self, name: core::Name, nbinders: u32) -> ty::Expr {
        match self.map[&name] {
            Entry::Bound { level, index } => {
                ty::Expr::bvar(ty::BoundVar::new(index, DebruijnIndex::new(nbinders - level - 1)))
            }
            Entry::Free(name) => ty::Expr::fvar(name),
        }
    }

    fn with_binders<R>(
        &mut self,
        binders: &[core::Ident],
        nbinders: u32,
        f: impl FnOnce(&mut Self, u32) -> R,
    ) -> R {
        for (index, binder) in binders.iter().enumerate() {
            self.insert(binder.name, Entry::Bound { index, level: nbinders });
        }
        let r = f(self, nbinders + 1);
        for binder in binders {
            self.map.remove(&binder.name);
        }
        r
    }
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'genv, 'tcx>) -> Self {
        Self { genv, name_map: NameMap::default() }
    }

    pub fn conv_fn_sig(genv: &GlobalEnv, fn_sig: core::FnSig) -> ty::Binders<ty::FnSig> {
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

        ty::Binders::new(ty::FnSig::new(requires, args, ret, ensures), params)
    }

    pub(crate) fn conv_enum_def(
        genv: &mut GlobalEnv,
        enum_def: core::EnumDef,
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

    fn conv_variant(&mut self, variant: core::VariantDef) -> PolyVariant {
        let sorts = self.conv_params(&variant.params);
        let fields = variant
            .fields
            .iter()
            .map(|ty| self.conv_ty(ty, 1))
            .collect_vec();
        let ret = self.conv_ty(&variant.ret, 1);
        let variant = ty::VariantDef::new(fields, ret);
        Binders::new(variant, sorts)
    }

    pub(crate) fn conv_struct_def(
        genv: &GlobalEnv,
        struct_def: &core::StructDef,
    ) -> Option<ty::PolyVariant> {
        let mut cx = ConvCtxt::new(genv);
        let sorts = cx.conv_params(&struct_def.refined_by);
        let def_id = struct_def.def_id;
        let rustc_adt = genv.tcx.adt_def(def_id);
        if let core::StructKind::Transparent { fields } = &struct_def.kind {
            let fields = iter::zip(fields, &rustc_adt.variant(VariantIdx::from_u32(0)).fields)
                .map(|(ty, field)| {
                    match ty {
                        Some(ty) => cx.conv_ty(ty, 1),
                        None => genv.default_type_of(field.did),
                    }
                })
                .collect_vec();

            let substs = genv
                .tcx
                .generics_of(struct_def.def_id)
                .params
                .iter()
                .map(|param| ty::Ty::param(ty::ParamTy { index: param.index, name: param.name }))
                .collect_vec();

            let idxs = sorts
                .iter()
                .enumerate()
                .map(|(idx, _)| ty::Expr::bvar(ty::BoundVar::innermost(idx)).into())
                .collect_vec();
            let ret = ty::Ty::indexed(ty::BaseTy::adt(genv.adt_def(def_id), substs), idxs);
            let variant = ty::VariantDef::new(fields, ret);
            Some(Binders::new(variant, sorts))
        } else {
            None
        }
    }

    fn conv_params(&mut self, params: &[core::Param]) -> Vec<ty::Sort> {
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

    fn conv_constr(&mut self, constr: &core::Constraint, nbinders: u32) -> ty::Constraint {
        match constr {
            core::Constraint::Type(loc, ty) => {
                ty::Constraint::Type(
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                    self.conv_ty(ty, nbinders),
                )
            }
            core::Constraint::Pred(e) => ty::Constraint::Pred(conv_expr(e, &self.name_map, 1)),
        }
    }

    pub fn conv_qualifier(qualifier: &core::Qualifier) -> ty::Qualifier {
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

        ty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    fn conv_ty(&mut self, ty: &core::Ty, nbinders: u32) -> ty::Ty {
        match ty {
            core::Ty::BaseTy(bty) => {
                let bty = self.conv_base_ty(bty, nbinders);
                let sorts = bty.sorts();
                if sorts.is_empty() {
                    ty::Ty::indexed(bty, vec![])
                } else {
                    let pred = ty::Binders::new(ty::Pred::tt(), sorts);
                    ty::Ty::exists(bty, pred)
                }
            }
            core::Ty::Indexed(bty, indices) => {
                let indices = indices
                    .indices
                    .iter()
                    .map(|idx| self.conv_index(idx, nbinders))
                    .collect_vec();
                ty::Ty::indexed(self.conv_base_ty(bty, nbinders), indices)
            }
            core::Ty::Exists(bty, binders, pred) => {
                let bty = self.conv_base_ty(bty, nbinders);
                self.name_map
                    .with_binders(binders, nbinders, |name_map, nbinders| {
                        let expr = conv_expr(pred, name_map, nbinders);
                        let pred = ty::Binders::new(ty::Pred::Expr(expr), bty.sorts());
                        ty::Ty::exists(bty, pred)
                    })
            }
            core::Ty::Ptr(loc) => {
                ty::Ty::ptr(
                    ty::RefKind::Mut,
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                )
            }
            core::Ty::Ref(rk, ty) => {
                ty::Ty::mk_ref(Self::conv_ref_kind(*rk), self.conv_ty(ty, nbinders))
            }
            core::Ty::Param(param) => ty::Ty::param(*param),
            core::Ty::Float(float_ty) => ty::Ty::float(*float_ty),
            core::Ty::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.conv_ty(ty, nbinders))
                    .collect_vec();
                ty::Ty::tuple(tys)
            }
            core::Ty::Never => ty::Ty::never(),
            core::Ty::Constr(pred, ty) => {
                let pred = conv_expr(pred, &self.name_map, nbinders);
                ty::Ty::constr(pred, self.conv_ty(ty, nbinders))
            }
        }
    }

    fn conv_index(&self, idx: &core::Index, nbinders: u32) -> ty::Index {
        ty::Index { expr: conv_expr(&idx.expr, &self.name_map, nbinders), is_binder: idx.is_binder }
    }

    fn conv_ref_kind(rk: core::RefKind) -> ty::RefKind {
        match rk {
            core::RefKind::Mut => ty::RefKind::Mut,
            core::RefKind::Shr => ty::RefKind::Shr,
        }
    }

    fn conv_base_ty(&mut self, bty: &core::BaseTy, nbinders: u32) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let generics = self.genv.generics_of(*did);
                let defaults = generics.params.iter().skip(substs.len()).map(|generic| {
                    match &generic.kind {
                        GenericParamDefKind::Type { has_default } => {
                            debug_assert!(has_default);
                            self.genv.default_type_of(generic.def_id)
                        }
                    }
                });
                let adt_def = self.genv.adt_def(*did);
                let substs = substs
                    .iter()
                    .map(|ty| self.conv_ty(ty, nbinders))
                    .chain(defaults);
                ty::BaseTy::adt(adt_def, substs)
            }
        }
    }
}

fn conv_expr(expr: &core::Expr, name_map: &NameMap, nbinders: u32) -> ty::Expr {
    match &expr.kind {
        core::ExprKind::Const(did, _) => ty::Expr::const_def_id(*did),
        core::ExprKind::Var(name, ..) => name_map.get(*name, nbinders),
        core::ExprKind::Literal(lit) => ty::Expr::constant(conv_lit(*lit)),
        core::ExprKind::BinaryOp(op, e1, e2) => {
            ty::Expr::binary_op(
                *op,
                conv_expr(e1, name_map, nbinders),
                conv_expr(e2, name_map, nbinders),
            )
        }
    }
}

fn conv_lit(lit: core::Lit) -> ty::Constant {
    match lit {
        core::Lit::Int(n) => ty::Constant::from(n),
        core::Lit::Bool(b) => ty::Constant::from(b),
    }
}

pub fn conv_sort(sort: core::Sort) -> ty::Sort {
    match sort {
        core::Sort::Int => ty::Sort::Int,
        core::Sort::Bool => ty::Sort::Bool,
        core::Sort::Loc => ty::Sort::Loc,
    }
}
