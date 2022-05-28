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
            Constr::Type(path, ty) => Constr::Type(self.subst_expr(path), self.subst_ty(ty)),
            Constr::Pred(e) => Constr::Pred(self.subst_expr(e)),
        }
    }

    pub fn subst_ty(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, indices) => {
                Ty::indexed(
                    self.subst_base_ty(bty),
                    indices
                        .iter()
                        .map(|idx| self.subst_index(idx))
                        .collect_vec(),
                )
            }
            TyKind::Exists(bty, pred) => Ty::exists(self.subst_base_ty(bty), self.subst_pred(pred)),
            TyKind::Float(float_ty) => Ty::float(*float_ty),
            TyKind::Ptr(path) => Ty::ptr(self.subst_expr(path)),
            TyKind::Param(param) => self.subst_ty_param(*param),
            TyKind::Ref(mode, ty) => Ty::mk_ref(*mode, self.subst_ty(ty)),
            TyKind::Uninit => ty.clone(),
            TyKind::Tuple(tys) => {
                let tys = tys.iter().map(|ty| self.subst_ty(ty)).collect_vec();
                Ty::tuple(tys)
            }
            TyKind::Never => Ty::never(),
            TyKind::Discr => Ty::discr(),
        }
    }

    fn subst_index(&self, idx: &Index) -> Index {
        // TODO(nilehmann) Does it make sense to keep the is_binder flat after substituting?
        Index { expr: self.subst_expr(&idx.expr), is_binder: idx.is_binder }
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
            ExprKind::FreeVar(name) => self.map.get(name).cloned().unwrap_or_else(|| expr.clone()),
            ExprKind::BinaryOp(op, e1, e2) => {
                Expr::binary_op(*op, self.subst_expr(e1), self.subst_expr(e2))
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, self.subst_expr(e)),
            ExprKind::TupleProj(tup, field) => {
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
            ExprKind::PathProj(e, field) => Expr::path_proj(self.subst_expr(e), *field),
            ExprKind::BoundVar(_) | ExprKind::Constant(_) => expr.clone(),
            ExprKind::Local(local) => Expr::local(*local),
        }
    }

    pub fn subst_loc(&self, loc: Loc) -> Loc {
        let loc_expr = self.subst_expr(&loc.to_expr());
        loc_expr
            .to_loc()
            .unwrap_or_else(|| panic!("substitution produces invalid loc: {loc_expr:?}"))
    }

    fn subst_ty_param(&self, param: ParamTy) -> Ty {
        self.types
            .get(param.index as usize)
            .cloned()
            .unwrap_or_else(|| Ty::param(param))
    }
}
