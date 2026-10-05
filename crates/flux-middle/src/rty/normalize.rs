use std::ops::ControlFlow;

use itertools::Itertools;
use rustc_data_structures::{fx::FxIndexSet, unord::UnordMap};
use rustc_hir::def_id::{CrateNum, DefIndex, LOCAL_CRATE};
use rustc_macros::{TyDecodable, TyEncodable};
use toposort_scc::IndexGraph;

use super::{ESpan, fold::TypeSuperFoldable};
use crate::{
    def_id::{FluxDefId, FluxId},
    global_env::GlobalEnv,
    rty::{
        Binder, Expr, ExprKind, SortArg,
        expr::SpecFuncKind,
        fold::{TypeFoldable, TypeFolder, TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
};

#[derive(TyEncodable, TyDecodable)]
pub struct NormalizedDefns {
    krate: CrateNum,
    inlined_bodies: UnordMap<FluxId<DefIndex>, Binder<Expr>>,
    /// Information about all function definitions both with a body and UIF
    info: UnordMap<FluxId<DefIndex>, FuncInfo>,
}

// This implementation is needed for `flux-metada::Tables`
impl Default for NormalizedDefns {
    fn default() -> Self {
        Self { krate: LOCAL_CRATE, inlined_bodies: UnordMap::default(), info: UnordMap::default() }
    }
}

// TODO(nilehmann) should we make an enum? most of the fields don't matter for UIFs
/// This type represents what we know about a flux-def *after*
/// normalization, i.e. after "inlining" all or some transitively
/// called flux-defs. Whether a flux-def is inlined is decided by
/// [`GlobalEnv::should_inline_fun`] in the current session.
#[derive(Clone, TyEncodable, TyDecodable)]
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
    inlined_bodies: UnordMap<FluxDefId, Binder<Expr>>,
    info: UnordMap<FluxDefId, FuncInfo>,
}

pub(super) struct Normalizer<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    inlining: Option<&'a InliningCtxt>,
}

impl NormalizedDefns {
    pub fn new(
        genv: GlobalEnv,
        krate: CrateNum,
        funs: &[(FluxDefId, Option<Binder<Expr>>, bool)],
    ) -> Result<Self, Vec<FluxDefId>> {
        // 1. Topologically sort the Defns
        let ds = toposort(krate, funs)?;

        // 2. Expand each defn in the sorted order
        let mut inlining =
            InliningCtxt { krate, inlined_bodies: UnordMap::default(), info: UnordMap::default() };
        for (rank, i) in ds.iter().enumerate() {
            let (id, body, hide) = &funs[*i];

            if let Some(body) = body {
                let body = body.fold_with(&mut Normalizer::new(genv, Some(&inlining)));

                inlining.inlined_bodies.insert(*id, body);
                inlining
                    .info
                    .insert(*id, FuncInfo { rank, hide: *hide, uif: false });
            } else {
                inlining
                    .info
                    .insert(*id, FuncInfo { rank, hide: *hide, uif: true });
            }
        }
        Ok(Self {
            krate,
            info: inlining
                .info
                .into_items()
                .map(|(id, info)| (id.index(), info))
                .collect(),
            inlined_bodies: inlining
                .inlined_bodies
                .into_items()
                .map(|(id, body)| (id.index(), body))
                .collect(),
        })
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

/// Returns
/// * either Ok(d1...dn) which are topologically sorted such that
///   forall i < j, di does not depend on i.e. "call" dj
/// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1
fn toposort<T>(
    krate: CrateNum,
    defns: &[(FluxDefId, Option<Binder<Expr>>, T)],
) -> Result<Vec<usize>, Vec<FluxDefId>> {
    // 1. Make a Symbol to Index map
    let s2i: UnordMap<FluxDefId, usize> = defns
        .iter()
        .enumerate()
        .map(|(i, defn)| (defn.0, i))
        .collect();

    // 2. Make the dependency graph
    let mut adj_list = Vec::with_capacity(defns.len());
    for defn in defns {
        if let Some(body) = &defn.1 {
            let deps = deps(body)
                .iter()
                .filter(|did| did.krate() == krate)
                .filter_map(|s| s2i.get(s).copied())
                .collect_vec();
            adj_list.push(deps);
        } else {
            adj_list.push(vec![]);
        }
    }
    let mut g = IndexGraph::from_adjacency_list(&adj_list);
    g.transpose();

    // 3. Topologically sort the graph
    match g.toposort_or_scc() {
        Ok(is) => Ok(is),
        Err(mut scc) => {
            let cycle = scc.pop().unwrap();
            Err(cycle.iter().map(|i| defns[*i].0).collect())
        }
    }
}

/// Returns all the flux-defs (of any crate) called in `body`
pub fn deps(body: &Binder<Expr>) -> FxIndexSet<FluxDefId> {
    struct DepsVisitor(FxIndexSet<FluxDefId>);
    impl TypeVisitor for DepsVisitor {
        fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
            if let ExprKind::App(func, ..) = expr.kind()
                && let ExprKind::GlobalFunc(SpecFuncKind::Def(did)) = func.kind()
            {
                self.0.insert(*did);
            }
            expr.super_visit_with(self)
        }
    }
    let mut visitor = DepsVisitor(Default::default());
    let _ = body.visit_with(&mut visitor);
    visitor.0
}

impl<'a, 'genv, 'tcx> Normalizer<'a, 'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>, inlining: Option<&'a InliningCtxt>) -> Self {
        Self { genv, inlining }
    }

    fn func_defn(&self, did: FluxDefId) -> Binder<Expr> {
        if let Some(inlining) = self.inlining
            && did.krate() == inlining.krate
        {
            inlining.inlined_bodies[&did].clone()
        } else {
            self.genv.inlined_body(did)
        }
    }

    fn should_inline(&self, did: FluxDefId) -> bool {
        let info = if let Some(inlining) = self.inlining
            && did.krate() == inlining.krate
        {
            &inlining.info[&did]
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
