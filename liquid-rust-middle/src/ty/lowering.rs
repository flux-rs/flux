use std::iter;

use crate::{
    global_env::GlobalEnv,
    ty::{self, VariantDef},
};
use itertools::Itertools;
use liquid_rust_common::index::{IndexGen, IndexVec};
use rustc_hash::FxHashMap;

use crate::core;

pub struct LoweringCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'tcx>,
    name_map: NameMap,
}

type NameMap = FxHashMap<core::Name, ty::Name>;

impl<'a, 'tcx> LoweringCtxt<'a, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'tcx>) -> Self {
        Self { genv, name_map: FxHashMap::default() }
    }

    pub fn lower_fn_sig(genv: &GlobalEnv, fn_sig: core::FnSig) -> ty::Binders<ty::FnSig> {
        let name_gen = IndexGen::new();

        let mut cx = LoweringCtxt::new(genv);

        let params = cx
            .lower_params(&name_gen, &fn_sig.params)
            .into_iter()
            .map(|param| param.sort)
            .collect_vec();

        let mut requires = vec![];
        for constr in fn_sig.requires {
            requires.push(cx.lower_constr(&constr));
        }

        let mut args = vec![];
        for ty in fn_sig.args {
            args.push(cx.lower_ty(&ty));
        }

        let mut ensures = vec![];
        for constr in fn_sig.ensures {
            ensures.push(cx.lower_constr(&constr));
        }

        let ret = cx.lower_ty(&fn_sig.ret);

        ty::Binders::bind_with_vars(ty::FnSig::new(requires, args, ret, ensures), params)
    }

    pub fn lower_adt_def(genv: &GlobalEnv, adt_def: &core::AdtDef) -> ty::AdtDef {
        let name_gen = IndexGen::new();
        let mut cx = LoweringCtxt::new(genv);

        let refined_by = cx.lower_params(&name_gen, &adt_def.refined_by);

        match &adt_def.kind {
            core::AdtDefKind::Transparent { variants: None, .. } => {
                genv.default_adt_def(adt_def.def_id)
            }
            core::AdtDefKind::Transparent { variants: Some(variants), .. } => {
                let rustc_adt_def = genv.tcx.adt_def(adt_def.def_id);
                let variants = iter::zip(variants, &rustc_adt_def.variants)
                    .map(|(variant, rustc_variant)| {
                        variant
                            .as_ref()
                            .map(|variant| cx.lower_variant_def(variant))
                            .unwrap_or_else(|| genv.default_variant_def(rustc_variant))
                    })
                    .collect_vec();
                ty::AdtDef::transparent(adt_def.def_id, refined_by, IndexVec::from_raw(variants))
            }
            core::AdtDefKind::Opaque { .. } => ty::AdtDef::opaque(adt_def.def_id, refined_by),
        }
    }

    fn lower_variant_def(&self, variant_def: &core::VariantDef) -> VariantDef {
        let fields = variant_def
            .fields
            .iter()
            .map(|ty| self.lower_ty(ty))
            .collect_vec();
        VariantDef::new(fields)
    }

    fn lower_constr(&self, constr: &core::Constr) -> ty::Constr {
        match constr {
            core::Constr::Type(loc, ty) => {
                ty::Constr::Type(ty::Expr::fvar(self.name_map[&loc.name]), self.lower_ty(ty))
            }
            core::Constr::Pred(e) => ty::Constr::Pred(lower_expr(e, &self.name_map, &[])),
        }
    }

    fn lower_params(
        &mut self,
        name_gen: &IndexGen<ty::Name>,
        params: &[core::Param],
    ) -> Vec<ty::Param> {
        params
            .iter()
            .map(|param| {
                let fresh = name_gen.fresh();
                self.name_map.insert(param.name.name, fresh);
                ty::Param { name: fresh, sort: lower_sort(param.sort) }
            })
            .collect()
    }

    pub fn lower_qualifer(qualifier: &core::Qualifier) -> ty::Qualifier {
        let name_gen = IndexGen::new();
        let mut args = Vec::new();

        let mut name_map = NameMap::default();

        for param in &qualifier.args {
            let fresh = name_gen.fresh();
            name_map.insert(param.name.name, fresh);
            let sort = lower_sort(param.sort);
            args.push((fresh, sort));
        }

        let expr = lower_expr(&qualifier.expr, &name_map, &[]);

        ty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    fn lower_ty(&self, ty: &core::Ty) -> ty::Ty {
        match ty {
            core::Ty::BaseTy(bty) => {
                let bty = self.lower_base_ty(bty);
                ty::Ty::exists(bty, ty::Pred::tt())
            }
            core::Ty::Indexed(bty, indices) => {
                let indices = indices
                    .indices
                    .iter()
                    .map(|idx| self.lower_index(idx))
                    .collect_vec();
                ty::Ty::indexed(self.lower_base_ty(bty), indices)
            }
            core::Ty::Exists(bty, binders, pred) => {
                let bty = self.lower_base_ty(bty);
                ty::Ty::exists(bty, lower_expr(pred, &self.name_map, binders))
            }
            core::Ty::Ptr(loc) => ty::Ty::ptr(ty::Loc::Free(self.name_map[&loc.name])),
            core::Ty::Ref(rk, ty) => ty::Ty::mk_ref(Self::lower_ref_kind(*rk), self.lower_ty(ty)),
            core::Ty::Param(param) => ty::Ty::param(*param),
            core::Ty::Float(float_ty) => ty::Ty::float(*float_ty),
            core::Ty::Tuple(tys) => {
                let tys = tys.iter().map(|ty| self.lower_ty(ty)).collect_vec();
                ty::Ty::tuple(tys)
            }
            core::Ty::Never => ty::Ty::never(),
        }
    }

    fn lower_index(&self, idx: &core::Index) -> ty::Index {
        ty::Index { expr: lower_expr(&idx.expr, &self.name_map, &[]), is_binder: idx.is_binder }
    }

    fn lower_ref_kind(rk: core::RefKind) -> ty::RefKind {
        match rk {
            core::RefKind::Mut => ty::RefKind::Mut,
            core::RefKind::Shr => ty::RefKind::Shr,
        }
    }

    fn lower_base_ty(&self, bty: &core::BaseTy) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let adt_def = self.genv.adt_def(*did);
                let substs = substs.iter().map(|ty| self.lower_ty(ty));
                ty::BaseTy::adt(adt_def, substs)
            }
        }
    }
}

fn lower_expr(expr: &core::Expr, name_map: &NameMap, binders: &[core::Ident]) -> ty::Expr {
    match &expr.kind {
        core::ExprKind::Var(name, ..) => {
            if let Some(idx) = binders.iter().position(|bind| bind.name == *name) {
                todo!()
                // ty::Expr::bvar(idx as u32)
            } else {
                ty::Expr::fvar(name_map[name])
            }
        }
        core::ExprKind::Literal(lit) => ty::Expr::constant(lower_lit(*lit)),
        core::ExprKind::BinaryOp(op, e1, e2) => {
            ty::Expr::binary_op(
                *op,
                lower_expr(e1, name_map, binders),
                lower_expr(e2, name_map, binders),
            )
        }
    }
}

fn lower_lit(lit: core::Lit) -> ty::Constant {
    match lit {
        core::Lit::Int(n) => ty::Constant::from(n),
        core::Lit::Bool(b) => ty::Constant::from(b),
    }
}

pub fn lower_sort(sort: core::Sort) -> ty::Sort {
    match sort {
        core::Sort::Int => ty::Sort::int(),
        core::Sort::Bool => ty::Sort::bool(),
        core::Sort::Loc => ty::Sort::loc(),
    }
}
