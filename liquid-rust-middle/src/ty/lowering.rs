use std::iter;

use crate::{
    global_env::GlobalEnv,
    ty::{self, DebruijnIndex, VariantDef},
};
use itertools::Itertools;
use liquid_rust_common::index::{IndexGen, IndexVec};
use rustc_hash::FxHashMap;

use crate::core;

pub struct LoweringCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'tcx>,
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

impl<'a, 'tcx> LoweringCtxt<'a, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'tcx>) -> Self {
        Self { genv, name_map: NameMap::default() }
    }

    pub fn lower_fn_sig(genv: &GlobalEnv, fn_sig: core::FnSig) -> ty::Binders<ty::FnSig> {
        let mut cx = LoweringCtxt::new(genv);

        let params = cx.lower_params(&fn_sig.params);

        let mut requires = vec![];
        for constr in fn_sig.requires {
            requires.push(cx.lower_constr(&constr, 1));
        }

        let mut args = vec![];
        for ty in fn_sig.args {
            args.push(cx.lower_ty(&ty, 1));
        }

        let mut ensures = vec![];
        for constr in fn_sig.ensures {
            ensures.push(cx.lower_constr(&constr, 1));
        }

        let ret = cx.lower_ty(&fn_sig.ret, 1);

        ty::Binders::new(ty::FnSig::new(requires, args, ret, ensures), params)
    }

    pub fn lower_adt_def(genv: &GlobalEnv, adt_def: &core::AdtDef) -> ty::AdtDef {
        let mut cx = LoweringCtxt::new(genv);

        let params = cx.lower_params(&adt_def.refined_by);

        let generics = genv.adt_def_generics(adt_def.def_id);

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
                ty::AdtDef::transparent(
                    adt_def.def_id,
                    generics,
                    params,
                    IndexVec::from_raw(variants),
                )
            }
            core::AdtDefKind::Opaque { .. } => ty::AdtDef::opaque(adt_def.def_id, generics, params),
        }
    }

    fn lower_variant_def(&mut self, variant_def: &core::VariantDef) -> VariantDef {
        let fields = variant_def
            .fields
            .iter()
            .map(|ty| self.lower_ty(ty, 1))
            .collect_vec();

        VariantDef::new(fields)
    }

    fn lower_params(&mut self, params: &[core::Param]) -> Vec<ty::Sort> {
        params
            .iter()
            .enumerate()
            .map(|(index, param)| {
                self.name_map
                    .insert(param.name.name, Entry::Bound { index, level: 0 });
                lower_sort(param.sort)
            })
            .collect()
    }

    fn lower_constr(&mut self, constr: &core::Constraint, nbinders: u32) -> ty::Constraint {
        match constr {
            core::Constraint::Type(loc, ty) => {
                ty::Constraint::Type(
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                    self.lower_ty(ty, nbinders),
                )
            }
            core::Constraint::Pred(e) => ty::Constraint::Pred(lower_expr(e, &self.name_map, 1)),
        }
    }

    pub fn lower_qualifer(qualifier: &core::Qualifier) -> ty::Qualifier {
        let mut name_map = NameMap::default();
        let name_gen = IndexGen::new();

        let args = qualifier
            .args
            .iter()
            .map(|param| {
                let fresh = name_gen.fresh();
                name_map.insert(param.name.name, fresh);
                (fresh, lower_sort(param.sort))
            })
            .collect_vec();

        let expr = lower_expr(&qualifier.expr, &name_map, 1);

        ty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    fn lower_ty(&mut self, ty: &core::Ty, nbinders: u32) -> ty::Ty {
        match ty {
            core::Ty::BaseTy(bty) => {
                let bty = self.lower_base_ty(bty, nbinders);
                ty::Ty::exists(bty, ty::Pred::tt())
            }
            core::Ty::Indexed(bty, indices) => {
                let indices = indices
                    .indices
                    .iter()
                    .map(|idx| self.lower_index(idx, nbinders))
                    .collect_vec();
                ty::Ty::indexed(self.lower_base_ty(bty, nbinders), indices)
            }
            core::Ty::Exists(bty, binders, pred) => {
                let bty = self.lower_base_ty(bty, nbinders);
                self.name_map
                    .with_binders(binders, nbinders, |name_map, nbinders| {
                        ty::Ty::exists(bty, lower_expr(pred, name_map, nbinders))
                    })
            }
            core::Ty::Ptr(loc) => {
                ty::Ty::ptr(
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                )
            }
            core::Ty::Ref(rk, ty) => {
                ty::Ty::mk_ref(Self::lower_ref_kind(*rk), self.lower_ty(ty, nbinders))
            }
            core::Ty::Param(param) => ty::Ty::param(*param),
            core::Ty::Float(float_ty) => ty::Ty::float(*float_ty),
            core::Ty::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.lower_ty(ty, nbinders))
                    .collect_vec();
                ty::Ty::tuple(tys)
            }
            core::Ty::Never => ty::Ty::never(),
        }
    }

    fn lower_index(&self, idx: &core::Index, nbinders: u32) -> ty::Index {
        ty::Index {
            expr: lower_expr(&idx.expr, &self.name_map, nbinders),
            is_binder: idx.is_binder,
        }
    }

    fn lower_ref_kind(rk: core::RefKind) -> ty::RefKind {
        match rk {
            core::RefKind::Mut => ty::RefKind::Mut,
            core::RefKind::Shr => ty::RefKind::Shr,
        }
    }

    fn lower_base_ty(&mut self, bty: &core::BaseTy, nbinders: u32) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let adt_def = self.genv.adt_def(*did);
                let substs = substs.iter().map(|ty| self.lower_ty(ty, nbinders));
                ty::BaseTy::adt(adt_def, substs)
            }
        }
    }
}

fn lower_expr(expr: &core::Expr, name_map: &NameMap, nbinders: u32) -> ty::Expr {
    match &expr.kind {
        core::ExprKind::Var(name, ..) => name_map.get(*name, nbinders),
        core::ExprKind::Literal(lit) => ty::Expr::constant(lower_lit(*lit)),
        core::ExprKind::BinaryOp(op, e1, e2) => {
            ty::Expr::binary_op(
                *op,
                lower_expr(e1, name_map, nbinders),
                lower_expr(e2, name_map, nbinders),
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
        core::Sort::Int => ty::Sort::Int,
        core::Sort::Bool => ty::Sort::Bool,
        core::Sort::Loc => ty::Sort::Loc,
    }
}
