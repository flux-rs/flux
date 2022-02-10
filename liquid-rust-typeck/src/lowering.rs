use crate::ty;
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct LoweringCtxt {
    params: FxHashMap<core::Name, ty::Name>,
    locs: FxHashMap<core::Name, ty::Name>,
}

impl LoweringCtxt {
    pub fn empty() -> Self {
        Self { params: FxHashMap::default(), locs: FxHashMap::default() }
    }

    pub fn lower_fn_sig(fn_sig: &core::FnSig) -> ty::FnSig {
        let name_gen = IndexGen::new();
        let fresh_kvar = &mut |_| unreachable!("inference predicate in top level function");

        let mut cx = LoweringCtxt::empty();

        let mut params = Vec::new();
        for param in &fn_sig.params {
            let fresh = name_gen.fresh();
            cx.params.insert(param.name.name, fresh);
            params.push(ty::Param {
                name: fresh,
                sort: lower_sort(param.sort),
                pred: cx.lower_expr(&param.pred).into(),
            });
        }

        let mut requires = vec![];
        for (loc, ty) in &fn_sig.requires {
            let fresh = name_gen.fresh();
            requires.push((fresh, cx.lower_ty(ty, fresh_kvar)));
            cx.locs.insert(*loc, fresh);
        }

        let mut args = vec![];
        for ty in &fn_sig.args {
            args.push(cx.lower_ty(ty, fresh_kvar))
        }

        let mut ensures = vec![];
        for (loc, ty) in &fn_sig.ensures {
            let loc = if let Some(loc) = cx.locs.get(loc) {
                *loc
            } else {
                let fresh = name_gen.fresh();
                cx.locs.insert(*loc, fresh);
                fresh
            };
            ensures.push((loc, cx.lower_ty(ty, fresh_kvar)));
        }

        let ret = cx.lower_ty(&fn_sig.ret, fresh_kvar);

        ty::FnSig { params, requires, args, ret, ensures }
    }

    pub fn lower_ty(
        &self,
        ty: &core::Ty,
        fresh_kvar: &mut impl FnMut(ty::Sort) -> ty::Pred,
    ) -> ty::Ty {
        match ty {
            core::Ty::Refine(bty, e) => {
                ty::TyKind::Refine(self.lower_base_ty(bty, fresh_kvar), self.lower_expr(e)).intern()
            }
            core::Ty::Exists(bty, pred) => {
                let pred = match pred {
                    core::Pred::Infer => fresh_kvar(lower_sort(bty.sort())),
                    core::Pred::Expr(e) => ty::Pred::Expr(self.lower_expr(e)),
                };
                ty::TyKind::Exists(self.lower_base_ty(bty, fresh_kvar), pred).intern()
            }
            core::Ty::StrgRef(loc) => {
                ty::TyKind::StrgRef(ty::Loc::Abstract(self.locs[loc])).intern()
            }
            core::Ty::Ref(ty) => ty::TyKind::Ref(self.lower_ty(ty, fresh_kvar)).intern(),
            core::Ty::Param(param) => ty::TyKind::Param(*param).intern(),
        }
    }

    fn lower_base_ty(
        &self,
        bty: &core::BaseTy,
        fresh_kvar: &mut impl FnMut(ty::Sort) -> ty::Pred,
    ) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let substs = substs.iter().map(|ty| self.lower_ty(ty, fresh_kvar)).collect();
                ty::BaseTy::Adt(*did, substs)
            }
        }
    }

    fn lower_expr(&self, expr: &core::Expr) -> ty::Expr {
        match &expr.kind {
            core::ExprKind::Var(var, ..) => ty::ExprKind::Var(self.lower_var(*var)).intern(),
            core::ExprKind::Literal(lit) => ty::ExprKind::Constant(self.lower_lit(*lit)).intern(),
            core::ExprKind::BinaryOp(op, e1, e2) => {
                ty::ExprKind::BinaryOp(lower_bin_op(*op), self.lower_expr(e1), self.lower_expr(e2))
                    .intern()
            }
        }
    }

    fn lower_var(&self, var: core::Var) -> ty::Var {
        match var {
            core::Var::Bound => ty::Var::Bound,
            core::Var::Free(name) => ty::Var::Free(self.params[&name]),
        }
    }

    fn lower_lit(&self, lit: core::Lit) -> ty::Constant {
        match lit {
            core::Lit::Int(n) => ty::Constant::from(n),
            core::Lit::Bool(b) => ty::Constant::from(b),
        }
    }
}

fn lower_sort(sort: core::Sort) -> ty::Sort {
    match sort {
        core::Sort::Int => ty::Sort::Int,
        core::Sort::Bool => ty::Sort::Bool,
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
    }
}
