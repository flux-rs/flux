use rustc_data_structures::unord::UnordMap;
use rustc_hir::def_id::{CrateNum, DefIndex};

use super::{ESpan, fold::TypeSuperFoldable};
use crate::{
    def_id::{FluxDefId, FluxId},
    global_env::GlobalEnv,
    rty::{
        Binder, Expr, ExprKind, SortArg, SpecFunc, SpecFuncs,
        expr::SpecFuncKind,
        fold::{TypeFoldable, TypeFolder},
    },
};

pub struct NormalizedDefns {
    krate: CrateNum,
    inlined_bodies: UnordMap<FluxId<DefIndex>, Binder<Expr>>,
    /// Information about all function definitions both with a body and UIF
    info: UnordMap<FluxId<DefIndex>, FuncInfo>,
}

// TODO(nilehmann) should we make an enum? most of the fields don't matter for UIFs
/// This type represents what we know about a flux-def *after*
/// normalization, i.e. after "inlining" all or some transitively
/// called flux-defs. Whether a flux-def is inlined is decided by
/// [`GlobalEnv::should_inline_fun`] in the current session.
#[derive(Clone)]
pub struct FuncInfo {
    /// Whether or not this function is uninterpreted by default
    /// This value is irrelevant of UIFs.
    pub hide: bool,
    /// The rank of this function in the topological sort of all the flux-defs, needed so
    /// we can specify the `define-fun` in the correct order, without any "forward"
    /// dependencies which the SMT solver cannot handle.
    pub rank: usize,
    /// Whether the function is a UIF
    pub uif: bool,
}

pub(super) struct InliningCtxt {
    krate: CrateNum,
    inlined_bodies: UnordMap<FluxId<DefIndex>, Binder<Expr>>,
    info: UnordMap<FluxId<DefIndex>, FuncInfo>,
}

pub(super) struct Normalizer<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    inlining: Option<&'a InliningCtxt>,
}

impl NormalizedDefns {
    pub fn new(genv: GlobalEnv, krate: CrateNum, funcs: &SpecFuncs) -> Self {
        // Expand each function in postorder, so its callees are already expanded
        let mut inlining =
            InliningCtxt { krate, inlined_bodies: UnordMap::default(), info: UnordMap::default() };
        for (rank, (id, func)) in funcs.postorder().enumerate() {
            let SpecFunc { body, hide } = func;

            if let Some(body) = body {
                let body = body.fold_with(&mut Normalizer::new(genv, Some(&inlining)));

                inlining.inlined_bodies.insert(id, body);
                inlining
                    .info
                    .insert(id, FuncInfo { rank, hide: *hide, uif: false });
            } else {
                inlining
                    .info
                    .insert(id, FuncInfo { rank, hide: *hide, uif: true });
            }
        }
        Self { krate, info: inlining.info, inlined_bodies: inlining.inlined_bodies }
    }

    pub fn func_info(&self, did: FluxDefId) -> FuncInfo {
        debug_assert_eq!(self.krate, did.krate());
        self.info.get(&did.index()).unwrap().clone()
    }

    pub fn inlined_body(&self, did: FluxDefId) -> Binder<Expr> {
        debug_assert_eq!(self.krate, did.krate());
        self.inlined_bodies.get(&did.index()).unwrap().clone()
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
        let info = if let Some(inlining) = self.inlining
            && did.krate() == inlining.krate
        {
            &inlining.info[&did.index()]
        } else {
            &self.genv.normalized_info(did)
        };
        !info.uif && !info.hide && self.genv.should_inline_fun(did)
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
