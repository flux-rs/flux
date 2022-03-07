use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;
use rustc_session::{Session, SessionDiagnostic};

use crate::{lowering::lower_sort, ty};

pub struct Wf<'a> {
    sess: &'a Session,
    adt_defs: &'a core::AdtDefs,
}

struct Env {
    sorts: FxHashMap<core::Name, ty::Sort>,
    bound_var_sort: Option<ty::Sort>,
}

impl Env {
    fn new(params: &[core::Param]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, lower_sort(param.sort)))
            .collect();
        Env { sorts, bound_var_sort: None }
    }

    fn with_bound<R>(&mut self, sort: ty::Sort, f: impl FnOnce(&Self) -> R) -> R {
        self.bound_var_sort = Some(sort);
        let r = f(self);
        self.bound_var_sort = None;
        r
    }
}

impl std::ops::Index<&'_ core::Var> for Env {
    type Output = ty::Sort;

    fn index(&self, var: &core::Var) -> &Self::Output {
        match var {
            core::Var::Bound => self.bound_var_sort.as_ref().unwrap(),
            core::Var::Free(name) => &self.sorts[name],
        }
    }
}

impl Wf<'_> {
    pub fn new<'a>(sess: &'a Session, adt_defs: &'a core::AdtDefs) -> Wf<'a> {
        Wf { sess, adt_defs }
    }

    pub fn check_fn_sig(&self, fn_sig: &core::FnSig) -> Result<(), ErrorReported> {
        let mut env = Env::new(&fn_sig.params);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty));

        let ensures = fn_sig
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ret = self.check_type(&mut env, &fn_sig.ret);

        args?;
        ret?;
        ensures?;

        Ok(())
    }

    pub fn check_qualifier(&self, qualifier: &core::Qualifier) -> Result<(), ErrorReported> {
        let mut env = Env::new(&qualifier.args);

        self.check_expr(&mut env, &qualifier.expr, ty::Sort::bool())
    }

    pub fn check_adt_def(&self, def: &core::AdtDef) -> Result<(), ErrorReported> {
        let mut env = Env::new(def.refined_by());

        if let core::AdtDef::Transparent { fields, .. } = def {
            fields
                .iter()
                .try_for_each_exhaust(|ty| self.check_type(&mut env, ty))?;
        }
        Ok(())
    }

    fn check_constr(&self, env: &mut Env, constr: &core::Constr) -> Result<(), ErrorReported> {
        match constr {
            core::Constr::Type(loc, ty) => {
                [self.check_loc(env, *loc), self.check_type(env, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            core::Constr::Pred(e) => self.check_expr(env, e, ty::Sort::bool()),
        }
    }

    fn check_type(&self, env: &mut Env, ty: &core::Ty) -> Result<(), ErrorReported> {
        match ty {
            core::Ty::Refine(bty, refine) => self.check_refine(env, refine, self.sort(bty)),
            core::Ty::Exists(bty, pred) => {
                env.with_bound(self.sort(bty), |env| self.check_pred(env, pred, ty::Sort::bool()))
            }
            core::Ty::StrgRef(loc) => self.check_loc(env, *loc),
            core::Ty::WeakRef(ty) | core::Ty::ShrRef(ty) => self.check_type(env, ty),
            core::Ty::Param(_) | core::Ty::Float(_) => Ok(()),
        }
    }

    fn check_refine(
        &self,
        env: &Env,
        refine: &core::Refine,
        expected: ty::Sort,
    ) -> Result<(), ErrorReported> {
        let found = self.synth_refine(env, refine)?;
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(Some(refine.span), expected, found))
        }
    }

    fn check_pred(
        &self,
        env: &Env,
        pred: &core::Pred,
        sort: ty::Sort,
    ) -> Result<(), ErrorReported> {
        match pred {
            core::Pred::Infer => Ok(()),
            core::Pred::Expr(e) => self.check_expr(env, e, sort),
        }
    }

    fn check_expr(
        &self,
        env: &Env,
        e: &core::Expr,
        expected: ty::Sort,
    ) -> Result<(), ErrorReported> {
        let found = self.synth_expr(env, e)?;
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, found))
        }
    }

    fn check_loc(&self, env: &Env, loc: core::Ident) -> Result<(), ErrorReported> {
        let found = env[&core::Var::Free(loc.name)].clone();
        if found == ty::Sort::loc() {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(
                Some(loc.source_info.0),
                ty::Sort::loc(),
                found,
            ))
        }
    }

    fn synth_refine(&self, env: &Env, refine: &core::Refine) -> Result<ty::Sort, ErrorReported> {
        let sorts: Vec<ty::Sort> = refine
            .exprs
            .iter()
            .map(|e| self.synth_expr(env, e))
            .try_collect_exhaust()?;
        Ok(ty::Sort::tuple(sorts))
    }

    fn synth_expr(&self, env: &Env, e: &core::Expr) -> Result<ty::Sort, ErrorReported> {
        match &e.kind {
            core::ExprKind::Var(var, ..) => Ok(env[var].clone()),
            core::ExprKind::Literal(lit) => Ok(self.synth_lit(*lit)),
            core::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(env, *op, e1, e2),
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
        op: core::BinOp,
        e1: &core::Expr,
        e2: &core::Expr,
    ) -> Result<ty::Sort, ErrorReported> {
        match op {
            core::BinOp::Or | core::BinOp::And | core::BinOp::Iff | core::BinOp::Imp => {
                self.check_expr(env, e1, ty::Sort::bool())?;
                self.check_expr(env, e2, ty::Sort::bool())?;
                Ok(ty::Sort::bool())
            }
            core::BinOp::Eq => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(ty::Sort::bool())
            }
            core::BinOp::Lt | core::BinOp::Le | core::BinOp::Gt | core::BinOp::Ge => {
                self.check_expr(env, e1, ty::Sort::int())?;
                self.check_expr(env, e2, ty::Sort::int())?;
                Ok(ty::Sort::bool())
            }
            core::BinOp::Add | core::BinOp::Sub | core::BinOp::Mod | core::BinOp::Mul => {
                self.check_expr(env, e1, ty::Sort::int())?;
                self.check_expr(env, e2, ty::Sort::int())?;
                Ok(ty::Sort::int())
            }
        }
    }

    fn synth_lit(&self, lit: core::Lit) -> ty::Sort {
        match lit {
            core::Lit::Int(_) => ty::Sort::int(),
            core::Lit::Bool(_) => ty::Sort::bool(),
        }
    }

    fn sort(&self, bty: &core::BaseTy) -> ty::Sort {
        match bty {
            core::BaseTy::Int(_) => ty::Sort::int(),
            core::BaseTy::Uint(_) => ty::Sort::int(),
            core::BaseTy::Bool => ty::Sort::bool(),
            core::BaseTy::Adt(def_id, _) => {
                if let Some(def) = def_id.as_local().and_then(|did| self.adt_defs.get(did)) {
                    ty::Sort::tuple(def.refined_by().iter().map(|param| lower_sort(param.sort)))
                } else {
                    ty::Sort::unit()
                }
            }
        }
    }

    fn emit_err<'a, T>(&'a self, err: impl SessionDiagnostic<'a>) -> Result<T, ErrorReported> {
        self.sess.emit_err(err);
        Err(ErrorReported)
    }
}

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    use crate::ty;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct SortMismatch {
        #[message = "mismatched sorts"]
        #[label = "expected `{expected}`, found `{found}`"]
        pub span: Option<Span>,
        pub expected: ty::Sort,
        pub found: ty::Sort,
    }

    impl SortMismatch {
        pub fn new(span: Option<Span>, expected: ty::Sort, found: ty::Sort) -> Self {
            Self { span, expected, found }
        }
    }
}
