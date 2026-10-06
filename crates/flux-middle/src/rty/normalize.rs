use rustc_data_structures::unord::UnordMap;
use rustc_hir::def_id::{CrateNum, DefIndex};

use super::{ESpan, fold::TypeSuperFoldable};
use crate::{
    def_id::{FluxDefId, FluxId},
    global_env::GlobalEnv,
    rty::{
        Binder, Expr, ExprKind, SortArg, SpecFuncs,
        expr::SpecFuncKind,
        fold::{TypeFoldable, TypeFolder},
    },
};

/// The bodies of the spec functions of a crate *after* inlining all or some of the spec functions
/// they (transitively) call. Whether a spec function is inlined is decided by
/// [`GlobalEnv::should_inline_fun`] in the current session.
///
/// Functions are identified by their index within the crate. Use [`GlobalEnv::inlined_body`] to
/// get the inlined body of a [`FluxDefId`].
pub struct NormalizedDefns {
    inlined_bodies: UnordMap<FluxId<DefIndex>, Binder<Expr>>,
}

pub(super) struct InliningCtxt {
    krate: CrateNum,
    inlined_bodies: UnordMap<FluxId<DefIndex>, Binder<Expr>>,
}

pub(super) struct Normalizer<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    inlining: Option<&'a InliningCtxt>,
}

impl NormalizedDefns {
    pub fn new(genv: GlobalEnv, krate: CrateNum, funcs: &SpecFuncs) -> Self {
        // Expand each function in postorder, so its callees are already expanded
        let mut inlining = InliningCtxt { krate, inlined_bodies: UnordMap::default() };
        for (id, func) in funcs.postorder() {
            if let Some(body) = &func.body {
                let body = body.fold_with(&mut Normalizer::new(genv, Some(&inlining)));
                inlining.inlined_bodies.insert(id, body);
            }
        }
        Self { inlined_bodies: inlining.inlined_bodies }
    }

    pub fn inlined_body(&self, id: FluxId<DefIndex>) -> Binder<Expr> {
        self.inlined_bodies[&id].clone()
    }
}

impl<'a, 'genv, 'tcx> Normalizer<'a, 'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>, inlining: Option<&'a InliningCtxt>) -> Self {
        Self { genv, inlining }
    }

    fn func_defn(&self, did: FluxDefId) -> Binder<Expr> {
        if let Some(inlining) = self.inlining
            && did.krate() == inlining.krate
        {
            inlining.inlined_bodies[&did.index()].clone()
        } else {
            self.genv.inlined_body(did)
        }
    }

    fn should_inline(&self, did: FluxDefId) -> bool {
        let func = self.genv.spec_func(did);
        !func.is_uif() && !func.hide && self.genv.should_inline_fun(did)
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
                let res = self.func_defn(*did).replace_bound_refts(args);
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

impl TypeFolder for Normalizer<'_, '_, '_> {
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
