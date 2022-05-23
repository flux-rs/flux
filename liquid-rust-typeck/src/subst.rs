use std::iter;

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{global_env::GlobalEnv, pure_ctxt::PureCtxt, ty::*, type_env::TypeEnv};

#[derive(Debug)]
pub struct Subst<'a> {
    map: FxHashMap<Name, Expr>,
    types: &'a [Ty],
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
            let e = pcx.push_binding(param.sort.clone(), &Pred::tt());
            subst.insert(param.name, e);
        }
        subst
    }

    pub fn insert(&mut self, from: Name, to: impl Into<Expr>) -> Option<Expr> {
        self.map.insert(from, to.into())
    }

    pub fn subst_fn_sig(&self, sig: &FnSig) -> FnSig {
        FnSig::new(
            sig.requires()
                .iter()
                .map(|constr| self.subst_constr(constr))
                .collect_vec(),
            sig.args().iter().map(|ty| self.subst_ty(ty)).collect_vec(),
            self.subst_ty(sig.ret()),
            sig.ensures()
                .iter()
                .map(|constr| self.subst_constr(constr))
                .collect_vec(),
        )
    }

    fn subst_constr(&self, constr: &Constr) -> Constr {
        match constr {
            Constr::Type(path, ty) => Constr::Type(self.subst_path(path), self.subst_ty(ty)),
            Constr::Pred(e) => Constr::Pred(self.subst_expr(e)),
        }
    }

    pub fn subst_ty(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, exprs) => {
                Ty::indexed(
                    self.subst_base_ty(bty),
                    exprs.iter().map(|e| self.subst_expr(e)).collect_vec(),
                )
            }
            TyKind::Exists(bty, pred) => Ty::exists(self.subst_base_ty(bty), self.subst_pred(pred)),
            TyKind::Float(float_ty) => Ty::float(*float_ty),
            TyKind::Ptr(path) => Ty::strg_ref(self.subst_path(path)),
            TyKind::Param(param) => self.subst_ty_param(*param),
            TyKind::Ref(mode, ty) => Ty::mk_ref(*mode, self.subst_ty(ty)),
            TyKind::Uninit(_) => ty.clone(),
            TyKind::Tuple(tys) => {
                let tys = tys.iter().map(|ty| self.subst_ty(ty)).collect_vec();
                Ty::tuple(tys)
            }
            TyKind::Never => Ty::never(),
            TyKind::Discr => Ty::discr(),
        }
    }

    pub fn subst_pred(&self, pred: &Pred) -> Pred {
        match pred {
            Pred::Kvars(kvars) => {
                let kvars = kvars.iter().map(|kvar| self.subst_kvar(kvar)).collect_vec();
                Pred::kvars(kvars)
            }
            Pred::Expr(e) => self.subst_expr(e).into(),
            Pred::Hole => Pred::Hole,
        }
    }

    fn subst_path(&self, path: &Path) -> Path {
        match path.loc {
            Loc::Local(_) => path.clone(),
            Loc::Free(name) => {
                match self.map.get(&name) {
                    Some(e) if let ExprKind::Path(inner) = e.kind() => {
                        let proj = inner
                            .projection()
                            .iter()
                            .chain(path.projection())
                            .copied()
                            .collect_vec();
                        Path::new(inner.loc, proj)
                    }
                    Some(e) if let ExprKind::Var(Var::Free(to)) = e.kind() => {
                        Path::new(Loc::Free(*to), path.projection())
                    }
                    Some(e) => {
                        panic!("invalid substitution in path `{path:?}`: `{:?}` -> `{e:?}`", path.loc)
                    }
                    None => path.clone(),
                }
            }
        }
    }

    fn subst_kvar(&self, KVar(kvid, args): &KVar) -> KVar {
        let args = args.iter().map(|arg| self.subst_expr(arg)).collect_vec();
        KVar::new(*kvid, args)
    }

    fn subst_base_ty(&self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, substs) => {
                let substs = substs.iter().map(|ty| self.subst_ty(ty));
                BaseTy::adt(adt_def.clone(), substs)
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
            ExprKind::Proj(tup, field) => {
                let tup = self.subst_expr(tup);
                // Opportunistically eta reduce the tuple
                match tup.kind() {
                    ExprKind::Tuple(exprs) => exprs[*field as usize].clone(),
                    _ => Expr::proj(tup, *field),
                }
            }
            ExprKind::Tuple(exprs) => {
                Expr::tuple(exprs.iter().map(|e| self.subst_expr(e)).collect_vec())
            }
            ExprKind::Path(path) => Expr::path(self.subst_path(path)),
        }
    }

    pub fn subst_var(&self, var: Var) -> Expr {
        match var {
            Var::Bound(_) => var.into(),
            Var::Free(name) => self.map.get(&name).cloned().unwrap_or_else(|| var.into()),
        }
    }

    pub fn subst_loc(&self, loc: Loc) -> Loc {
        match loc {
            Loc::Local(local) => Loc::Local(local),
            Loc::Free(name) => {
                match self.map.get(&name) {
                    Some(e) if let ExprKind::Path(path) = e.kind() && path.projection().is_empty() => {
                        path.loc
                    }
                    Some(e) if let ExprKind::Var(Var::Free(to)) = e.kind() => {
                        Loc::Free(*to)
                    }
                    Some(e) => {
                        panic!("invalid loc substitution: `{loc:?}` -> `{e:?}`")
                    }
                    None => Loc::Free(name)
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
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        env: &TypeEnv,
        actuals: &[Ty],
        fn_sig: &Binders<FnSig>,
    ) -> Result<(), InferenceError> {
        assert!(actuals.len() == fn_sig.value().args().len());
        let params = fn_sig.params().iter().map(|param| param.name).collect();

        let requires = fn_sig
            .value()
            .requires()
            .iter()
            .filter_map(|constr| {
                if let Constr::Type(path, ty) = constr {
                    Some((path.clone(), ty.clone()))
                } else {
                    None
                }
            })
            .collect();

        for (actual, formal) in actuals.iter().zip(fn_sig.value().args().iter()) {
            self.infer_from_tys(genv, pcx, &params, env, actual, &requires, formal);
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

    #[allow(clippy::too_many_arguments)]
    fn infer_from_tys(
        &mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        params: &FxHashSet<Name>,
        env: &TypeEnv,
        ty1: &TyS,
        requires: &FxHashMap<Path, Ty>,
        ty2: &TyS,
    ) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(_, exprs1), TyKind::Indexed(_, exprs2)) => {
                for (e1, e2) in iter::zip(exprs1, exprs2) {
                    self.infer_from_exprs(params, e1, e2);
                }
            }
            (TyKind::Exists(bty1, p), TyKind::Indexed(_, exprs2)) => {
                // HACK(nilehmann) we should probably remove this once we have proper unpacking of &mut refs
                let sorts = genv.sorts(bty1);
                let exprs1 = pcx.push_bindings(&sorts, p);
                for (e1, e2) in iter::zip(exprs1, exprs2) {
                    self.infer_from_exprs(params, &e1, e2);
                }
            }
            (TyKind::Ptr(path1), TyKind::Ref(_, ty2)) => {
                self.infer_from_tys(genv, pcx, params, env, &env.lookup_path(path1), requires, ty2);
            }
            (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
                self.infer_from_paths(params, path1, path2);
                self.infer_from_tys(
                    genv,
                    pcx,
                    params,
                    env,
                    &env.lookup_path(path1),
                    requires,
                    &requires[path2],
                );
            }
            (TyKind::Ref(mode1, ty1), TyKind::Ref(mode2, ty2)) => {
                debug_assert_eq!(mode1, mode2);
                self.infer_from_tys(genv, pcx, params, env, ty1, requires, ty2);
            }
            _ => {}
        }
    }

    fn infer_from_paths(&mut self, _params: &FxHashSet<Name>, path1: &Path, path2: &Path) {
        // TODO(nilehmann) we should probably do something with _params
        if !path2.projection().is_empty() {
            return;
        }
        if let Loc::Free(name) = path2.loc {
            let new = Expr::path(path1.clone());
            match self.insert(name, new.clone()) {
                Some(old) if old != new => {
                    todo!("ambiguous instantiation for location parameter`",);
                }
                _ => {}
            }
        }
    }

    pub fn infer_from_exprs(&mut self, params: &FxHashSet<Name>, e1: &Expr, e2: &Expr) {
        match (e1.kind(), e2.kind()) {
            (_, ExprKind::Var(Var::Free(name))) if params.contains(name) => {
                if let Some(old_e) = self.insert(*name, e1.clone()) {
                    if &old_e != e2 {
                        todo!(
                            "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                            *name,
                            old_e,
                            e1
                        )
                    }
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
