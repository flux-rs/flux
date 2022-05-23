use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::ty::*;

#[derive(Debug)]
pub struct Subst<'a> {
    map: FxHashMap<Name, Expr>,
    types: &'a [Ty],
}

impl Subst<'_> {
    pub fn empty() -> Self {
        Subst { types: &[], map: FxHashMap::default() }
    }

    pub fn with_type_substs(types: &[Ty]) -> Subst {
        Subst { types, map: FxHashMap::default() }
    }

    pub fn insert(&mut self, from: Name, to: impl Into<Expr>) -> Option<Expr> {
        self.map.insert(from, to.into())
    }

    pub fn contains(&self, from: Name) -> bool {
        self.map.contains_key(&from)
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
}
