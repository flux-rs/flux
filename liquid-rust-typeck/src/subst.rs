use rustc_hash::{FxHashMap, FxHashSet};

use crate::{pure_ctxt::PureCtxt, ty::*, type_env::TypeEnv};

#[derive(Debug)]
pub struct Subst<'a> {
    map: FxHashMap<Name, LocOrExpr>,
    types: &'a [Ty],
}

enum LocOrExpr {
    Loc(Loc),
    Expr(Expr),
}

#[derive(Debug, Eq, PartialEq)]
pub struct InferenceError(Name);

impl Subst<'_> {
    pub fn empty() -> Self {
        Subst { types: &[], map: FxHashMap::default() }
    }

    pub fn with_type_substs(types: &[Ty]) -> Subst {
        Subst { types, map: FxHashMap::default() }
    }

    pub fn with_fresh_names(pcx: &mut PureCtxt, params: &[Param]) -> Self {
        let mut subst = Self::empty();
        for param in params {
            let fresh = pcx.push_binding(param.sort.clone(), |_| Expr::tt());
            subst.insert_param(param, fresh);
        }
        subst
    }

    pub fn insert_name_subst(&mut self, name: Name, sort: Sort, to: Name) {
        match sort.kind() {
            SortKind::Loc => {
                self.map.insert(name, LocOrExpr::Loc(Loc::Abstract(to)));
            }
            _ => {
                self.map.insert(name, LocOrExpr::Expr(Var::Free(to).into()));
            }
        }
    }

    pub fn insert_expr_subst(&mut self, name: Name, expr: Expr) {
        self.map.insert(name, LocOrExpr::Expr(expr));
    }

    pub fn insert_loc_subst(&mut self, name: Name, to: impl Into<Loc>) {
        self.map.insert(name, LocOrExpr::Loc(to.into()));
    }

    pub fn insert_param(&mut self, param: &Param, to: Name) {
        self.insert_name_subst(param.name, param.sort.clone(), to);
    }

    pub fn get_expr(&self, name: Name) -> Expr {
        match self.map.get(&name) {
            Some(LocOrExpr::Expr(expr)) => expr.clone(),
            _ => panic!("expected expr"),
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
            TyKind::Refine(bty, e) => Ty::refine(self.subst_base_ty(bty), self.subst_expr(e)),
            TyKind::Exists(bty, pred) => Ty::exists(self.subst_base_ty(bty), self.subst_pred(pred)),
            TyKind::Float(float_ty) => Ty::float(*float_ty),
            TyKind::StrgRef(loc) => Ty::strg_ref(self.subst_loc(*loc)),
            TyKind::Param(param) => self.subst_ty_param(*param),
            TyKind::WeakRef(ty) => Ty::weak_ref(self.subst_ty(ty)),
            TyKind::ShrRef(ty) => Ty::shr_ref(self.subst_ty(ty)),
            TyKind::Uninit(_) => ty.clone(),
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
                Expr::binary_op(*op, self.subst_expr(e1), self.subst_expr(e2))
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, self.subst_expr(e)),
            ExprKind::Proj(e, field) => Expr::proj(self.subst_expr(e), *field),
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
            .unwrap_or_else(|| Ty::param(param))
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

        self.check_inference(params.into_iter())
    }

    pub fn check_inference(
        &self,
        params: impl Iterator<Item = Name>,
    ) -> Result<(), InferenceError> {
        for name in params {
            if !self.map.contains_key(&name) {
                return Err(InferenceError(name));
            }
        }
        Ok(())
    }

    pub fn infer_from_tys(&mut self, params: &FxHashSet<Name>, ty1: &TyS, ty2: &TyS) {
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

    pub fn infer_from_exprs(&mut self, params: &FxHashSet<Name>, e1: &Expr, e2: &Expr) {
        match (e1.kind(), e2.kind()) {
            (_, ExprKind::Var(Var::Free(name))) if params.contains(name) => {
                match self.map.insert(*name, LocOrExpr::Expr(e1.clone())) {
                    Some(LocOrExpr::Expr(old_e)) => {
                        if &old_e != e2 {
                            todo!(
                                "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                                *name,
                                old_e,
                                e1
                            )
                        }
                    }
                    Some(LocOrExpr::Loc(old_l)) => {
                        panic!("subsitution of loc for expr: `{name:?}`: old `{old_l:?}`, new: `{e1:?}`")
                    }
                    None => {}
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
