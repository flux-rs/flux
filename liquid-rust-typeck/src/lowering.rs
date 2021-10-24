use crate::ty::{self, Expr};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct LowerCtxt<'a> {
    name_gen: &'a IndexGen<ty::Var>,
}

type Subst = FxHashMap<core::Name, ty::Expr>;

impl<'a> LowerCtxt<'a> {
    fn new(name_gen: &'a IndexGen<ty::Var>) -> Self {
        Self { name_gen }
    }

    pub fn lower_with_fresh_names(
        name_gen: &IndexGen<ty::Var>,
        fn_sig: &core::FnSig,
    ) -> (Vec<(ty::Var, ty::Sort, ty::Pred)>, Vec<ty::Ty>, ty::Ty) {
        let mut subst = FxHashMap::default();
        let cx = LowerCtxt::new(name_gen);

        let mut params = Vec::new();
        for param in &fn_sig.params {
            let fresh = name_gen.fresh();
            subst.insert(param.name.name, ty::ExprKind::Var(fresh).intern());
            let expr = param
                .pred
                .as_ref()
                .map(|e| cx.lower_expr(e, &subst))
                .unwrap_or(Expr::tt());
            params.push((fresh, param.sort, ty::Pred::Expr(expr)));
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
        name_gen: &IndexGen<ty::Var>,
        mut subst: Subst,
        fn_sig: &core::FnSig,
    ) -> (Vec<ty::Pred>, Vec<ty::Ty>, ty::Ty) {
        let cx = LowerCtxt::new(name_gen);

        let mut params = Vec::new();
        for param in &fn_sig.params {
            let expr = param
                .pred
                .as_ref()
                .map(|e| cx.lower_expr(e, &subst))
                .unwrap_or(Expr::tt());
            params.push(ty::Pred::Expr(expr));
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
            core::Ty::Refine(bty, r) => {
                ty::TyKind::Refine(*bty, self.lower_refine(r, subst)).intern()
            }
            core::Ty::Exists(bty, evar, e) => {
                let fresh = self.name_gen.fresh();
                subst.insert(*evar, ty::ExprKind::Var(fresh).intern());
                let e = self.lower_expr(e, subst);
                subst.remove(evar);
                ty::TyKind::Exists(*bty, fresh, e).intern()
            }
        }
    }

    fn lower_refine(&self, refine: &core::Refine, subst: &Subst) -> ty::Expr {
        match refine {
            core::Refine::Var(ident) => subst.get(&ident.name).unwrap().clone(),
            core::Refine::Literal(lit) => ty::ExprKind::Constant(self.lower_lit(*lit)).intern(),
        }
    }

    fn lower_expr(&self, expr: &core::Expr, subst: &Subst) -> ty::Expr {
        match &expr.kind {
            core::ExprKind::Var(ident) => self.lower_ident(ident, subst),
            core::ExprKind::Literal(lit) => ty::ExprKind::Constant(self.lower_lit(*lit)).intern(),
            core::ExprKind::BinaryOp(op, e1, e2) => ty::ExprKind::BinaryOp(
                map_bin_op(*op),
                self.lower_expr(e1, subst),
                self.lower_expr(e2, subst),
            )
            .intern(),
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
        core::BinOp::Ge => ty::BinOp::Ge,
        core::BinOp::Lt => ty::BinOp::Lt,
        core::BinOp::Le => ty::BinOp::Le,
        core::BinOp::Or => ty::BinOp::Or,
        core::BinOp::And => ty::BinOp::And,
    }
}
