use crate::{
    ty::{self, context::LrCtxt, Sort},
    unification::UnificationCtxt,
};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct LowerCtxt<'a> {
    lr: &'a LrCtxt,
}

type Subst = FxHashMap<core::Name, VarOrEVar>;

enum VarOrEVar {
    Var(ty::Var),
    Evar(ty::EVar),
}

impl LowerCtxt<'_> {
    pub fn lower_with_fresh_names(
        lr: &LrCtxt,
        name_gen: &IndexGen<ty::Var>,
        fn_sig: &core::FnSig,
    ) -> (Vec<(ty::Var, ty::Sort, ty::Pred)>, Vec<ty::Ty>, ty::Ty) {
        Self::lower(lr, |_| name_gen.fresh(), fn_sig)
    }

    pub fn lower_with_fresh_evars(
        lr: &LrCtxt,
        unification_cx: &mut UnificationCtxt,
        fn_sig: &core::FnSig,
    ) -> (Vec<(ty::EVar, ty::Sort, ty::Pred)>, Vec<ty::Ty>, ty::Ty) {
        Self::lower(lr, |sort| unification_cx.new_evar(sort), fn_sig)
    }

    fn lower<T, F>(
        lr: &LrCtxt,
        mut mk_fresh: F,
        fn_sig: &core::FnSig,
    ) -> (Vec<(T, ty::Sort, ty::Pred)>, Vec<ty::Ty>, ty::Ty)
    where
        F: FnMut(Sort) -> T,
        T: Into<VarOrEVar> + Copy,
    {
        let mut subst = FxHashMap::default();
        let cx = LowerCtxt { lr };

        let mut params = Vec::new();
        for param in &fn_sig.params {
            let fresh = mk_fresh(param.sort);
            subst.insert(param.name.name, fresh.into());
            params.push((
                fresh,
                param.sort,
                ty::Pred::Expr(cx.lower_expr(&param.pred, &subst)),
            ));
        }

        let args = fn_sig
            .args
            .iter()
            .map(|ty| cx.lower_ty(ty, &subst))
            .collect();

        let ret = cx.lower_ty(&fn_sig.ret, &subst);

        (params, args, ret)
    }

    fn lower_ty(&self, ty: &core::Ty, subst: &Subst) -> ty::Ty {
        match ty {
            core::Ty::Int(n, int_ty) => self.lr.mk_int(self.lower_refine(n, subst), *int_ty),
        }
    }

    fn lower_refine(&self, refine: &core::Refine, subst: &Subst) -> ty::Refine {
        match refine {
            core::Refine::Var(ident) => match *subst.get(&ident.name).unwrap() {
                VarOrEVar::Var(var) => ty::Refine::Expr(self.lr.mk_var(var)),
                VarOrEVar::Evar(evar) => ty::Refine::EVar(evar),
            },
            core::Refine::Literal(lit) => {
                ty::Refine::Expr(self.lr.mk_constant(self.lower_lit(*lit)))
            }
        }
    }

    fn lower_expr(&self, expr: &core::Expr, subst: &Subst) -> ty::Expr {
        let lr = self.lr;
        match &expr.kind {
            core::ExprKind::Var(ident) => self.lower_ident(ident, subst),
            core::ExprKind::Literal(lit) => lr.mk_constant(self.lower_lit(*lit)),
            core::ExprKind::BinaryOp(op, e1, e2) => lr.mk_bin_op(
                map_bin_op(*op),
                self.lower_expr(e1, subst),
                self.lower_expr(e2, subst),
            ),
        }
    }

    fn lower_ident(&self, ident: &core::Ident, subst: &Subst) -> ty::Expr {
        match *subst.get(&ident.name).unwrap() {
            VarOrEVar::Var(var) => self.lr.mk_var(var),
            VarOrEVar::Evar(evar) => self.lr.mk_evar(evar),
        }
    }

    fn lower_lit(&self, lit: core::Lit) -> ty::Constant {
        match &lit.kind {
            core::LitKind::Int(n) => ty::Constant::from(*n),
        }
    }
}

fn map_bin_op(op: core::BinOp) -> ty::BinOp {
    match op {
        core::BinOp::Eq => ty::BinOp::Eq,
        core::BinOp::Add => ty::BinOp::Add,
    }
}

impl From<ty::EVar> for VarOrEVar {
    fn from(v: ty::EVar) -> Self {
        Self::Evar(v)
    }
}

impl From<ty::Var> for VarOrEVar {
    fn from(v: ty::Var) -> Self {
        Self::Var(v)
    }
}
