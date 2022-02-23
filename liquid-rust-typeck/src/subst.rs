use std::collections::HashSet;

use rustc_hash::FxHashMap;

use crate::{
    pure_ctxt::PureCtxt,
    ty::*,
    type_env::{BasicBlockEnv, TypeEnv},
};

#[derive(Debug)]
pub struct Subst {
    map: FxHashMap<Name, LocOrExpr>,
    types: Vec<Ty>,
}

enum LocOrExpr {
    Loc(Loc),
    Expr(Expr),
}

pub struct InferenceError;

impl Subst {
    pub fn empty() -> Self {
        Self { types: vec![], map: FxHashMap::default() }
    }

    pub fn with_type_substs(types: Vec<Ty>) -> Self {
        Self { types, map: FxHashMap::default() }
    }

    pub fn with_fresh_names(pcx: &mut PureCtxt, params: &[Param]) -> Self {
        let mut subst = Self::empty();
        for param in params {
            let fresh = pcx.push_binding(param.sort.clone(), |_| Expr::tt());
            subst.insert_param(param, fresh);
        }
        subst
    }

    pub fn insert_param(&mut self, param: &Param, to: Name) {
        match param.sort.kind() {
            SortKind::Loc => {
                self.map
                    .insert(param.name, LocOrExpr::Loc(Loc::Abstract(to)));
            }
            _ => {
                self.map
                    .insert(param.name, LocOrExpr::Expr(Var::Free(to).into()));
            }
        }
    }

    pub fn subst_fn_sig(&self, sig: &FnSig) -> FnSig {
        FnSig {
            requires: sig
                .requires
                .iter()
                .map(|constr| self.subst_constr(constr))
                .collect(),
            args: sig.args.iter().map(|ty| self.subst_ty(ty)).collect(),
            ret: self.subst_ty(&sig.ret),
            ensures: sig
                .ensures
                .iter()
                .map(|constr| self.subst_constr(constr))
                .collect(),
        }
    }

    fn subst_constr(&self, constr: &Constr) -> Constr {
        match constr {
            Constr::Type(loc, ty) => Constr::Type(self.subst_loc(*loc), self.subst_ty(ty)),
            Constr::Pred(e) => Constr::Pred(self.subst_expr(e)),
        }
    }

    pub fn subst_ty(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Refine(bty, e) => {
                TyKind::Refine(self.subst_base_ty(bty), self.subst_expr(e)).intern()
            }
            TyKind::Exists(bty, pred) => {
                TyKind::Exists(self.subst_base_ty(bty), self.subst_pred(pred)).intern()
            }
            TyKind::StrgRef(loc) => TyKind::StrgRef(self.subst_loc(*loc)).intern(),
            TyKind::Param(param) => self.subst_ty_param(*param),
            TyKind::WeakRef(ty) => TyKind::WeakRef(self.subst_ty(ty)).intern(),
            TyKind::ShrRef(ty) => TyKind::ShrRef(self.subst_ty(ty)).intern(),
            TyKind::Uninit => ty.clone(),
        }
    }

    pub fn subst_pred(&self, pred: &Pred) -> Pred {
        match pred {
            Pred::KVar(kvid, args) => {
                let args = args.iter().map(|arg| self.subst_expr(arg));
                Pred::kvar(*kvid, args)
            }
            Pred::Expr(e) => self.subst_expr(e).into(),
        }
    }

    fn subst_base_ty(&self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(did, substs) => {
                let substs = substs.iter().map(|ty| self.subst_ty(ty)).collect();
                BaseTy::Adt(*did, substs)
            }
            _ => bty.clone(),
        }
    }

    pub fn subst_expr(&self, expr: &Expr) -> Expr {
        match expr.kind() {
            ExprKind::Var(var) => self.subst_var(*var),
            ExprKind::Constant(_) => expr.clone(),
            ExprKind::BinaryOp(op, e1, e2) => {
                ExprKind::BinaryOp(*op, self.subst_expr(e1), self.subst_expr(e2)).intern()
            }
            ExprKind::UnaryOp(op, e) => ExprKind::UnaryOp(*op, self.subst_expr(e)).intern(),
            ExprKind::Proj(e, field) => ExprKind::Proj(self.subst_expr(e), *field).intern(),
            ExprKind::Tuple(exprs) => Expr::tuple(exprs.iter().map(|e| self.subst_expr(e))),
        }
    }

    pub fn subst_var(&self, var: Var) -> Expr {
        match var {
            Var::Bound => var.into(),
            Var::Free(name) => {
                match self.map.get(&name) {
                    Some(LocOrExpr::Loc(loc)) => {
                        panic!("substituting loc for var: `{name:?}` -> `{loc:?}`")
                    }
                    Some(LocOrExpr::Expr(expr)) => expr.clone(),
                    None => var.into(),
                }
            }
        }
    }

    pub fn subst_loc(&self, loc: Loc) -> Loc {
        match loc {
            Loc::Local(local) => Loc::Local(local),
            Loc::Abstract(name) => {
                match self.map.get(&name) {
                    Some(LocOrExpr::Expr(e)) => {
                        panic!("substituting expr for loc: `{loc:?}` -> `{e:?}`")
                    }
                    Some(LocOrExpr::Loc(loc)) => *loc,
                    None => Loc::Abstract(name),
                }
            }
        }
    }

    fn subst_ty_param(&self, param: ParamTy) -> Ty {
        self.types
            .get(param.index as usize)
            .cloned()
            .unwrap_or_else(|| TyKind::Param(param).intern())
    }

    pub fn infer_from_fn_call(
        &mut self,
        env: &TypeEnv,
        actuals: &[Ty],
        fn_sig: &Binders<FnSig>,
    ) -> Result<(), InferenceError> {
        assert!(actuals.len() == fn_sig.value.args.len());
        let params = fn_sig.params.iter().map(|param| param.name).collect();

        for (actual, formal) in actuals.iter().zip(fn_sig.value.args.iter()) {
            self.infer_from_tys(&params, actual, formal);
        }

        for constr in &fn_sig.value.requires {
            if let Constr::Type(loc, required) = constr {
                let actual = env.lookup_loc(self.subst_loc(*loc));
                self.infer_from_tys(&params, &actual, required);
            }
        }

        self.check_inference(&fn_sig.params)
    }

    pub fn infer_from_bb_env(
        &mut self,
        env: &TypeEnv,
        bb_env: &BasicBlockEnv,
    ) -> Result<(), InferenceError> {
        let params = bb_env.params.iter().map(|param| param.name).collect();
        for (loc, binding2) in bb_env.env.iter() {
            let ty1 = env.lookup_loc(*loc);
            self.infer_from_tys(&params, &ty1, &binding2.ty());
        }
        self.check_inference(&bb_env.params)
    }

    fn check_inference(&self, params: &[Param]) -> Result<(), InferenceError> {
        for param in params {
            if !self.map.contains_key(&param.name) {
                return Err(InferenceError);
            }
        }
        Ok(())
    }

    fn infer_from_tys(&mut self, params: &HashSet<Name>, ty1: &TyS, ty2: &TyS) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(_bty1, e1), TyKind::Refine(_bty2, e2)) => {
                self.infer_from_exprs(params, e1, e2);
            }
            (TyKind::StrgRef(loc), TyKind::StrgRef(Loc::Abstract(name))) => {
                match self.map.insert(*name, LocOrExpr::Loc(*loc)) {
                    Some(LocOrExpr::Loc(old_loc)) if &old_loc != loc => {
                        todo!("ambiguous instantiation for location parameter`",);
                    }
                    Some(_) => panic!("subsitution of expression for loc"),
                    _ => {}
                }
            }
            (TyKind::ShrRef(ty1), TyKind::ShrRef(ty2)) => {
                self.infer_from_tys(params, ty1, ty2);
            }
            _ => {}
        }
    }

    fn infer_from_exprs(&mut self, params: &HashSet<Name>, e1: &Expr, e2: &Expr) {
        match (e1.kind(), e2.kind()) {
            (_, ExprKind::Var(Var::Free(name))) if params.contains(name) => {
                match self.map.insert(*name, LocOrExpr::Expr(e1.clone())) {
                    Some(LocOrExpr::Expr(old_e)) if &old_e != e1 => {
                        todo!(
                            "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                            *name,
                            old_e,
                            e1
                        )
                    }
                    Some(_) => panic!("subsitution of loc for var"),
                    _ => {}
                }
            }
            (ExprKind::Tuple(exprs1), ExprKind::Tuple(exprs2)) => {
                debug_assert_eq!(exprs1.len(), exprs2.len());
                for (e1, e2) in exprs1.iter().zip(exprs2) {
                    self.infer_from_exprs(params, e1, e2);
                }
            }
            _ => {}
        }
    }
}

mod pretty {
    use super::*;
    use crate::pretty::*;

    impl Pretty for LocOrExpr {
        fn fmt(&self, cx: &PPrintCx, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            define_scoped!(cx, f);
            match self {
                LocOrExpr::Loc(loc) => w!("loc${:?}", loc),
                LocOrExpr::Expr(e) => {
                    let e = if cx.simplify_exprs { e.simplify() } else { e.clone() };
                    if e.is_atom() {
                        w!("expr${:?}", e)
                    } else {
                        w!("expr$({:?})", e)
                    }
                }
            }
        }
    }

    impl_debug_with_default_cx!(LocOrExpr);
}
