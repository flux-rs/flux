use super::{ESpan, fold::TypeSuperFoldable};
use crate::{
    def_id::FluxDefId,
    global_env::GlobalEnv,
    rty::{Expr, ExprKind, SortArg, SpecFunc, expr::SpecFuncKind, fold::TypeFolder},
};

pub(super) struct Reducer<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
}

impl<'genv, 'tcx> Reducer<'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>) -> Self {
        Self { genv }
    }

    fn should_inline(&self, did: FluxDefId) -> bool {
        matches!(self.genv.spec_func(did), SpecFunc::Defined { hide: false, .. })
            && self.genv.should_inline_fun(did)
    }

    fn at_base(expr: Expr, espan: Option<ESpan>) -> Expr {
        match espan {
            Some(espan) => BaseSpanner::new(espan).fold_expr(&expr),
            None => expr,
        }
    }

    fn app(
        &mut self,
        func: &Expr,
        sort_args: &[SortArg],
        args: &[Expr],
        espan: Option<ESpan>,
    ) -> Expr {
        match func.kind() {
            ExprKind::GlobalFunc(SpecFuncKind::Def(did)) if self.should_inline(*did) => {
                let res = self.genv.inlined_body(*did).replace_bound_refts(args);
                Self::at_base(res, espan)
            }
            ExprKind::Abs(lam) => {
                let res = lam.apply(args);
                Self::at_base(res, espan)
            }
            _ => Expr::app(func.clone(), sort_args.into(), args.into()).at_opt(espan),
        }
    }
}

impl TypeFolder for Reducer<'_, '_> {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        let expr = expr.super_fold_with(self);
        let span = expr.span();
        match expr.kind() {
            ExprKind::App(func, sorts, args) => self.app(func, sorts, args, span),
            ExprKind::FieldProj(e, proj) => e.proj_and_reduce(*proj),
            _ => expr,
        }
    }
}

struct BaseSpanner {
    espan: ESpan,
}

impl BaseSpanner {
    fn new(espan: ESpan) -> Self {
        Self { espan }
    }
}

impl TypeFolder for BaseSpanner {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        expr.super_fold_with(self).at_base(self.espan)
    }
}
