use crate::ty::{self, Path, VariantDef};
use itertools::Itertools;
use liquid_rust_common::index::{IndexGen, IndexVec};
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct LoweringCtxt {
    name_map: FxHashMap<core::Name, ty::Name>,
}

impl LoweringCtxt {
    pub fn empty() -> Self {
        Self { name_map: FxHashMap::default() }
    }

    pub fn lower_fn_sig(fn_sig: core::FnSig) -> ty::Binders<ty::FnSig> {
        let name_gen = IndexGen::new();

        let mut cx = LoweringCtxt::empty();

        let params = cx.lower_params(&name_gen, &fn_sig.params);

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

        ty::Binders::new(params, ty::FnSig::new(requires, args, ret, ensures))
    }

    pub fn lower_adt_def(adt_def: &core::AdtDef) -> ty::AdtDef {
        let name_gen = IndexGen::new();
        let mut cx = LoweringCtxt::empty();

        let refined_by = cx.lower_params(&name_gen, adt_def.refined_by());

        match adt_def {
            core::AdtDef::Transparent { variants, .. } => {
                let variants = variants
                    .iter()
                    .map(|variant| cx.lower_variant_def(variant))
                    .collect_vec();
                ty::AdtDef::transparent(refined_by, IndexVec::from_raw(variants))
            }
            core::AdtDef::Opaque { .. } => ty::AdtDef::opaque(refined_by),
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
                ty::Constr::Type(
                    Path::from(ty::Loc::Free(self.name_map[&loc.name])),
                    self.lower_ty(ty),
                )
            }
            core::Constr::Pred(e) => ty::Constr::Pred(self.lower_expr(e)),
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

        let mut cx = LoweringCtxt::empty();

        for param in &qualifier.args {
            let fresh = name_gen.fresh();
            cx.name_map.insert(param.name.name, fresh);
            let sort = lower_sort(param.sort);
            args.push((fresh, sort));
        }

        let expr = cx.lower_expr(&qualifier.expr);

        ty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    pub fn lower_ty(&self, ty: &core::Ty) -> ty::Ty {
        match ty {
            core::Ty::Indexed(bty, refine) => {
                let exprs = refine
                    .exprs
                    .iter()
                    .map(|e| self.lower_expr(e))
                    .collect_vec();
                ty::Ty::refine(self.lower_base_ty(bty), exprs)
            }
            core::Ty::Exists(bty, pred) => {
                let bty = self.lower_base_ty(bty);
                let pred = match pred {
                    core::Pred::Hole => ty::Pred::Hole,
                    core::Pred::Expr(e) => ty::Pred::Expr(self.lower_expr(e)),
                };
                ty::Ty::exists(bty, pred)
            }
            core::Ty::Ptr(loc) => ty::Ty::strg_ref(ty::Loc::Free(self.name_map[&loc.name])),
            core::Ty::Ref(rk, ty) => ty::Ty::mk_ref(Self::lower_ref_kind(*rk), self.lower_ty(ty)),
            core::Ty::Param(param) => ty::Ty::param(*param),
            core::Ty::Float(float_ty) => ty::Ty::float(*float_ty),
        }
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
                let substs = substs.iter().map(|ty| self.lower_ty(ty));
                ty::BaseTy::adt(*did, substs)
            }
        }
    }

    fn lower_expr(&self, expr: &core::Expr) -> ty::Expr {
        match &expr.kind {
            core::ExprKind::Var(var, ..) => ty::Expr::var(self.lower_var(*var)),
            core::ExprKind::Literal(lit) => ty::Expr::constant(self.lower_lit(*lit)),
            core::ExprKind::BinaryOp(op, e1, e2) => {
                ty::Expr::binary_op(lower_bin_op(*op), self.lower_expr(e1), self.lower_expr(e2))
            }
        }
    }

    fn lower_var(&self, var: core::Var) -> ty::Var {
        match var {
            core::Var::Bound(idx) => ty::Var::Bound(idx),
            core::Var::Free(name) => ty::Var::Free(self.name_map[&name]),
        }
    }

    fn lower_lit(&self, lit: core::Lit) -> ty::Constant {
        match lit {
            core::Lit::Int(n) => ty::Constant::from(n),
            core::Lit::Bool(b) => ty::Constant::from(b),
        }
    }
}

pub fn lower_sort(sort: core::Sort) -> ty::Sort {
    match sort {
        core::Sort::Int => ty::Sort::int(),
        core::Sort::Bool => ty::Sort::bool(),
        core::Sort::Loc => ty::Sort::loc(),
    }
}

fn lower_bin_op(op: core::BinOp) -> ty::BinOp {
    match op {
        core::BinOp::Iff => ty::BinOp::Iff,
        core::BinOp::Imp => ty::BinOp::Imp,
        core::BinOp::Or => ty::BinOp::Or,
        core::BinOp::And => ty::BinOp::And,
        core::BinOp::Eq => ty::BinOp::Eq,
        core::BinOp::Gt => ty::BinOp::Gt,
        core::BinOp::Ge => ty::BinOp::Ge,
        core::BinOp::Lt => ty::BinOp::Lt,
        core::BinOp::Le => ty::BinOp::Le,
        core::BinOp::Add => ty::BinOp::Add,
        core::BinOp::Sub => ty::BinOp::Sub,
        core::BinOp::Mod => ty::BinOp::Mod,
        core::BinOp::Mul => ty::BinOp::Mul,
    }
}
