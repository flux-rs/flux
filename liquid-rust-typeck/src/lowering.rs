use crate::ty::{self, context::LrCtxt};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct LowerCtxt<'a> {
    lr: &'a LrCtxt,
    name_gen: &'a IndexGen<ty::Var>,
}

type Subst = FxHashMap<core::Name, ty::Expr>;

impl<'a> LowerCtxt<'a> {
    fn new(lr: &'a LrCtxt, name_gen: &'a IndexGen<ty::Var>) -> Self {
        Self { lr, name_gen }
    }

    pub fn lower_with_fresh_names(
        lr: &LrCtxt,
        name_gen: &IndexGen<ty::Var>,
        fn_sig: &core::FnSig,
    ) -> (Vec<(ty::Var, ty::Sort, ty::Pred)>, Vec<ty::Ty>, ty::Ty) {
        let mut subst = FxHashMap::default();
        let cx = LowerCtxt::new(lr, name_gen);

        let mut params = Vec::new();
        for param in &fn_sig.params {
            let fresh = name_gen.fresh();
            subst.insert(param.name.name, lr.mk_var(fresh));
            params.push((
                fresh,
                param.sort,
                ty::Pred::Expr(cx.lower_expr(&param.pred, &subst)),
            ));
        }

        let args = fn_sig
            .args
            .iter()
            .map(|ty| cx.lower_ty(ty, &mut subst))
            .collect();

        let ret = cx.lower_ty(&fn_sig.ret, &mut subst);

        (params, args, ret)
    }

    pub fn lower_with_subst(
        lr: &LrCtxt,
        name_gen: &IndexGen<ty::Var>,
        mut subst: Subst,
        fn_sig: &core::FnSig,
    ) -> (Vec<ty::Pred>, Vec<ty::Ty>, ty::Ty) {
        let cx = LowerCtxt::new(lr, name_gen);

        let mut params = Vec::new();
        for param in &fn_sig.params {
            params.push(ty::Pred::Expr(cx.lower_expr(&param.pred, &subst)));
        }

        let args = fn_sig
            .args
            .iter()
            .map(|ty| cx.lower_ty(ty, &mut subst))
            .collect();

        let ret = cx.lower_ty(&fn_sig.ret, &mut subst);

        (params, args, ret)
    }

    fn lower_ty(&self, ty: &core::Ty, subst: &mut Subst) -> ty::Ty {
        match ty {
            core::Ty::Refine(bty, r) => self.lr.mk_refine(*bty, self.lower_refine(r, subst)),
            core::Ty::Exists(bty, evar, e) => {
                let fresh = self.name_gen.fresh();
                subst.insert(*evar, self.lr.mk_var(fresh));
                let e = self.lower_expr(e, subst);
                subst.remove(evar);
                self.lr.mk_exists(*bty, fresh, e)
            }
        }
    }

    fn lower_refine(&self, refine: &core::Refine, subst: &Subst) -> ty::Expr {
        match refine {
            core::Refine::Var(ident) => subst.get(&ident.name).unwrap().clone(),
            core::Refine::Literal(lit) => self.lr.mk_constant(self.lower_lit(*lit)),
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
        subst.get(&ident.name).unwrap().clone()
    }

    fn lower_lit(&self, lit: core::Lit) -> ty::Constant {
        match &lit.kind {
            core::LitKind::Int(n) => ty::Constant::from(*n),
            core::LitKind::Bool(b) => ty::Constant::from(*b),
        }
    }
}

fn map_bin_op(op: core::BinOp) -> ty::BinOp {
    match op {
        core::BinOp::Eq => ty::BinOp::Eq,
        core::BinOp::Add => ty::BinOp::Add,
        core::BinOp::Gt => ty::BinOp::Gt,
    }
}
