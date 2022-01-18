use crate::{constraint_builder::Cursor, ty, type_env::TypeEnv};
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct Subst {
    locations: FxHashMap<core::Name, ty::Loc>,
    exprs: FxHashMap<core::Name, ty::Expr>,
    types: Vec<ty::Ty>,
}

pub struct InferenceError;

impl Subst {
    pub fn with_empty_type_substs() -> Self {
        Self {
            exprs: FxHashMap::default(),
            locations: FxHashMap::default(),
            types: vec![],
        }
    }

    pub fn with_type_substs(cursor: &mut Cursor, types: &[core::Ty]) -> Self {
        let mut subst = Subst::with_empty_type_substs();
        subst.types.reserve(types.len());
        for ty in types {
            let ty = subst.lower_ty(cursor, ty);
            subst.types.push(ty);
        }
        subst
    }

    pub fn insert_expr(&mut self, name: core::Name, expr: impl Into<ty::Expr>) {
        self.exprs.insert(name, expr.into());
    }

    pub fn insert_loc(&mut self, name: core::Name, region: impl Into<ty::Loc>) {
        self.locations.insert(name, region.into());
    }

    pub fn infer_from_fn_call(
        &mut self,
        env: &TypeEnv,
        actuals: &[ty::Ty],
        fn_sig: &core::FnSig,
    ) -> Result<(), InferenceError> {
        assert!(actuals.len() == fn_sig.args.len());

        for (actual, formal) in actuals.iter().zip(fn_sig.args.iter()) {
            self.infer_from_tys(actual.clone(), formal);
        }

        for (loc, required) in &fn_sig.requires {
            let actual = env.lookup_loc(self.lower_loc(*loc).unwrap()).unwrap();
            self.infer_from_tys(actual, required);
        }

        self.check_inference(fn_sig)
    }

    fn check_inference(&self, fn_sig: &core::FnSig) -> Result<(), InferenceError> {
        for param in &fn_sig.params {
            if !self.exprs.contains_key(&param.name.name) {
                return Err(InferenceError);
            }
        }

        for (region, _) in &fn_sig.requires {
            if !self.locations.contains_key(region) {
                return Err(InferenceError);
            }
        }
        Ok(())
    }

    fn infer_from_tys(&mut self, ty1: ty::Ty, ty2: &core::Ty) {
        match (ty1.kind(), ty2) {
            (
                ty::TyKind::Refine(_bty1, e),
                core::Ty::Refine(
                    _bty2,
                    core::Expr {
                        kind: core::ExprKind::Var(core::Var::Free(name), symbol, ..),
                        ..
                    },
                ),
            ) => {
                // debug_assert!(bty1 == bty2);
                match self.exprs.insert(*name, e.clone()) {
                    Some(old_e) if &old_e != e => {
                        todo!("ambiguous instantiation for parameter `{}`", symbol)
                    }
                    _ => {}
                }
            }
            (ty::TyKind::StrgRef(loc1), core::Ty::MutRef(loc2)) => {
                match self.locations.insert(*loc2, *loc1) {
                    Some(old_region) if &old_region != loc1 => {
                        todo!("ambiguous instantiation for region parameter`",);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    pub fn lower_loc(&self, name: core::Name) -> Option<ty::Loc> {
        self.locations.get(&name).cloned()
    }

    pub fn lower_ty(&mut self, cursor: &mut Cursor, ty: &core::Ty) -> ty::Ty {
        match ty {
            core::Ty::Refine(bty, e) => {
                ty::TyKind::Refine(self.lower_base_ty(cursor, bty), self.lower_expr(e)).intern()
            }
            core::Ty::Exists(bty, pred) => {
                let pred = match pred {
                    core::Pred::Infer => cursor.fresh_kvar(bty.sort()),
                    core::Pred::Expr(e) => ty::Pred::Expr(self.lower_expr(e)),
                };
                ty::TyKind::Exists(self.lower_base_ty(cursor, bty), pred).intern()
            }
            core::Ty::MutRef(loc) => ty::TyKind::StrgRef(self.locations[loc]).intern(),
            core::Ty::Param(param) => self
                .types
                .get(param.index as usize)
                .cloned()
                .unwrap_or_else(|| ty::TyKind::Param(*param).intern()),
        }
    }

    pub fn lower_base_ty(&mut self, cursor: &mut Cursor, bty: &core::BaseTy) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let substs = substs.iter().map(|ty| self.lower_ty(cursor, ty)).collect();
                ty::BaseTy::Adt(*did, substs)
            }
        }
    }

    pub fn lower_expr(&self, expr: &core::Expr) -> ty::Expr {
        match &expr.kind {
            core::ExprKind::Var(var, _, _) => self.lower_var(*var),
            core::ExprKind::Literal(lit) => ty::ExprKind::Constant(self.lower_lit(*lit)).intern(),
            core::ExprKind::BinaryOp(op, e1, e2) => {
                ty::ExprKind::BinaryOp(lower_bin_op(*op), self.lower_expr(e1), self.lower_expr(e2))
                    .intern()
            }
        }
    }

    fn lower_var(&self, var: core::Var) -> ty::Expr {
        match var {
            core::Var::Bound => ty::Var::Bound.into(),
            core::Var::Free(name) => self.exprs[&name].clone(),
        }
    }

    fn lower_lit(&self, lit: core::Lit) -> ty::Constant {
        match lit {
            core::Lit::Int(n) => ty::Constant::from(n),
            core::Lit::Bool(b) => ty::Constant::from(b),
        }
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
        core::BinOp::Mod => ty::BinOp::Mod,
    }
}
