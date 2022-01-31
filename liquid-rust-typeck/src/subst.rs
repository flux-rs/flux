use std::collections::HashSet;

use rustc_hash::FxHashMap;

use crate::{
    ty::*,
    type_env::{BasicBlockEnv, TypeEnv},
};

#[derive(Debug)]
pub struct Subst {
    exprs: FxHashMap<Var, Expr>,
    locs: FxHashMap<Loc, Loc>,
    types: Vec<Ty>,
}

pub struct InferenceError;

impl Subst {
    pub fn empty() -> Self {
        Self {
            exprs: FxHashMap::default(),
            locs: FxHashMap::default(),
            types: vec![],
        }
    }

    pub fn with_type_substs(types: Vec<Ty>) -> Self {
        Self {
            exprs: FxHashMap::default(),
            locs: FxHashMap::default(),
            types,
        }
    }

    pub fn insert_expr(&mut self, var: Var, expr: impl Into<Expr>) {
        self.exprs.insert(var, expr.into());
    }

    pub fn insert_loc(&mut self, from: Loc, to: Loc) {
        self.locs.insert(from, to);
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
            TyKind::Ref(ty) => TyKind::Ref(self.subst_ty(ty)).intern(),
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
        }
    }

    fn subst_var(&self, var: Var) -> Expr {
        self.exprs.get(&var).cloned().unwrap_or_else(|| var.into())
    }

    pub fn subst_loc(&self, loc: Loc) -> Loc {
        self.locs.get(&loc).cloned().unwrap_or(loc)
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
        fn_sig: &FnSig,
    ) -> Result<(), InferenceError> {
        assert!(actuals.len() == fn_sig.args.len());
        let params = fn_sig
            .params
            .iter()
            .map(|param| param.name.into())
            .collect();

        for (actual, formal) in actuals.iter().zip(fn_sig.args.iter()) {
            self.infer_from_tys(&params, actual.clone(), formal.clone());
        }

        for (loc, required) in &fn_sig.requires {
            let loc = Loc::Abstract(*loc);
            let actual = env.lookup_loc(self.subst_loc(loc)).unwrap();
            self.infer_from_tys(&params, actual, required.clone());
        }

        self.check_inference(&fn_sig.params, &fn_sig.requires)
    }

    pub fn infer_from_bb_env(
        &mut self,
        env: &TypeEnv,
        bb_env: &BasicBlockEnv,
    ) -> Result<(), InferenceError> {
        let params = bb_env
            .params
            .iter()
            .map(|param| param.name.into())
            .collect();
        for (loc, ty2) in &bb_env.bindings {
            let ty1 = env.lookup_loc(*loc).unwrap();
            self.infer_from_tys(&params, ty1, ty2.clone());
        }
        self.check_inference(&bb_env.params, &[])
    }

    fn check_inference(
        &self,
        params: &[Param],
        requires: &[(Name, Ty)],
    ) -> Result<(), InferenceError> {
        for param in params {
            if !self.exprs.contains_key(&param.name.into()) {
                return Err(InferenceError);
            }
        }

        for (loc, _) in requires {
            if !self.locs.contains_key(&Loc::Abstract(*loc)) {
                return Err(InferenceError);
            }
        }
        Ok(())
    }

    fn infer_from_tys(&mut self, params: &HashSet<Var>, ty1: Ty, ty2: Ty) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(_bty1, e1), TyKind::Refine(_bty2, e2)) => {
                if let ExprKind::Var(var) = e2.kind() {
                    if !params.contains(var) {
                        return;
                    }
                    match self.exprs.insert(*var, e1.clone()) {
                        Some(old_e) if &old_e != e1 => {
                            todo!(
                                "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                                *var,
                                old_e,
                                e1
                            )
                        }
                        _ => {}
                    }
                }
            }
            (TyKind::StrgRef(loc1), TyKind::StrgRef(loc2)) => {
                match self.locs.insert(*loc2, *loc1) {
                    Some(old_loc) if &old_loc != loc1 => {
                        todo!("ambiguous instantiation for location parameter`",);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}
