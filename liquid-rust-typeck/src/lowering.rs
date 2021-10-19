use crate::ty::{self, context::LrCtxt};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ty as core;
use quickscope::ScopeMap;
use rustc_span::Symbol;

pub struct LowerCtxt<'a> {
    lr: &'a LrCtxt,
    name_gen: &'a IndexGen<ty::Var>,
    name_map: ScopeMap<Symbol, ty::Var>,
}

impl LowerCtxt<'_> {
    pub fn lower(lr: &LrCtxt, name_gen: &IndexGen<ty::Var>, fn_sig: &core::FnSig) -> ty::FnSig {
        let mut wf = LowerCtxt {
            lr,
            name_gen,
            name_map: ScopeMap::new(),
        };
        wf.lower_fn_sig(fn_sig)
    }

    fn lower_fn_sig(&mut self, fn_sig: &core::FnSig) -> ty::FnSig {
        let params = fn_sig
            .params
            .iter()
            .map(|(ident, rty)| {
                let fresh = self.name_gen.fresh();
                self.name_map.push_layer();
                self.name_map.define(ident.symbol, fresh);
                (fresh, self.check_rtype(rty))
            })
            .collect();

        let args = fn_sig.args.iter().map(|ty| self.check_ty(ty)).collect();

        let ret = self.check_ty(&fn_sig.ret);

        ty::FnSig { params, args, ret }
    }

    fn check_ty(&mut self, ty: &core::Ty) -> ty::Ty {
        match ty {
            core::Ty::Int(n, int_ty) => self.lr.mk_int(self.check_expr(n), *int_ty),
        }
    }

    fn check_rtype(&mut self, rty: &core::RType) -> ty::RType {
        ty::RType {
            sort: rty.sort,
            refine: ty::Refine::Pred(self.check_expr(&rty.pred)),
        }
    }

    fn check_expr(&mut self, expr: &core::Expr) -> ty::Expr {
        let lr = self.lr;
        match &expr.kind {
            core::ExprKind::Var(ident) => lr.mk_var(*self.name_map.get(&ident.symbol).unwrap()),
            core::ExprKind::Literal(core::Lit {
                kind: core::LitKind::Int(n),
                ..
            }) => lr.mk_constant(ty::Constant::from(*n)),
            core::ExprKind::BinaryOp(op, e1, e2) => {
                lr.mk_bin_op(map_bin_op(*op), self.check_expr(e1), self.check_expr(e2))
            }
        }
    }
}

fn map_bin_op(op: core::BinaryOp) -> ty::BinOp {
    match op {
        core::BinaryOp::Eq => ty::BinOp::Eq,
    }
}
