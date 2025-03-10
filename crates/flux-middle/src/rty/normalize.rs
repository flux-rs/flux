use std::ops::ControlFlow;

use itertools::Itertools;
use rustc_data_structures::{fx::FxIndexSet, unord::UnordMap};
use toposort_scc::IndexGraph;

use super::{ESpan, fold::TypeSuperFoldable};
use crate::{
    FluxDefId, FluxLocalDefId,
    fhir::SpecFuncKind,
    global_env::GlobalEnv,
    rty::{
        Binder, Expr, ExprKind, SpecFunc,
        fold::{TypeFoldable, TypeFolder, TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
};

#[derive(Default)]
pub struct NormalizedDefns {
    defns: UnordMap<FluxLocalDefId, SpecFunc>,
}

pub(super) struct Normalizer<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    defs: Option<&'a UnordMap<FluxLocalDefId, SpecFunc>>,
}

impl NormalizedDefns {
    pub fn new(genv: GlobalEnv, defns: &[SpecFunc]) -> Result<Self, Vec<FluxLocalDefId>> {
        // 1. Topologically sort the Defns
        let ds = toposort(defns)?;

        // 2. Expand each defn in the sorted order
        let mut normalized = UnordMap::default();
        for i in ds {
            let defn = &defns[i];
            let body = defn
                .body
                .fold_with(&mut Normalizer::new(genv, Some(&normalized)));
            normalized.insert(defn.def_id.expect_local(), SpecFunc { body, ..*defn });
        }
        Ok(Self { defns: normalized })
    }

    pub fn func_defn(&self, did: FluxLocalDefId) -> &SpecFunc {
        self.defns.get(&did).unwrap()
    }
}

/// Returns
/// * either Ok(d1...dn) which are topologically sorted such that
///   forall i < j, di does not depend on i.e. "call" dj
/// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1
fn toposort(defns: &[SpecFunc]) -> Result<Vec<usize>, Vec<FluxLocalDefId>> {
    // 1. Make a Symbol to Index map
    let s2i: UnordMap<FluxLocalDefId, usize> = defns
        .iter()
        .enumerate()
        .map(|(i, defn)| (defn.def_id.expect_local(), i))
        .collect();

    // 2. Make the dependency graph
    let mut adj_list: Vec<Vec<usize>> = Vec::with_capacity(defns.len());
    for defn in defns {
        let deps = local_deps(&defn.body);
        let ddeps = deps
            .iter()
            .filter_map(|s| s2i.get(s).copied())
            .collect_vec();
        adj_list.push(ddeps);
    }
    let mut g = IndexGraph::from_adjacency_list(&adj_list);
    g.transpose();

    // 3. Topologically sort the graph
    match g.toposort_or_scc() {
        Ok(is) => Ok(is),
        Err(mut scc) => {
            let cycle = scc.pop().unwrap();
            Err(cycle
                .iter()
                .map(|i| defns[*i].def_id.expect_local())
                .collect())
        }
    }
}

fn local_deps(body: &Binder<Expr>) -> FxIndexSet<FluxLocalDefId> {
    struct DepsVisitor(FxIndexSet<FluxLocalDefId>);
    impl TypeVisitor for DepsVisitor {
        fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
            if let ExprKind::App(func, _) = expr.kind()
                && let ExprKind::GlobalFunc(SpecFuncKind::Def(did)) = func.kind()
                && let Some(did) = did.as_local()
            {
                self.0.insert(did);
            }
            expr.super_visit_with(self)
        }
    }
    let mut visitor = DepsVisitor(Default::default());
    body.visit_with(&mut visitor);
    visitor.0
}

impl<'a, 'genv, 'tcx> Normalizer<'a, 'genv, 'tcx> {
    pub(super) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        defs: Option<&'a UnordMap<FluxLocalDefId, SpecFunc>>,
    ) -> Self {
        Self { genv, defs }
    }

    fn func_defn(&self, did: FluxDefId) -> &SpecFunc {
        if let Some(defs) = self.defs
            && let Some(local_id) = did.as_local()
        {
            defs.get(&local_id).unwrap()
        } else {
            self.genv.normalized_defn(did)
        }
    }

    fn at_base(expr: Expr, espan: Option<ESpan>) -> Expr {
        match espan {
            Some(espan) => BaseSpanner::new(espan).fold_expr(&expr),
            None => expr,
        }
    }

    fn app(&mut self, func: &Expr, args: &[Expr], espan: Option<ESpan>) -> Expr {
        match func.kind() {
            ExprKind::GlobalFunc(SpecFuncKind::Def(did)) => {
                let res = self.func_defn(*did).body.replace_bound_refts(args);
                Self::at_base(res, espan)
            }
            ExprKind::Abs(lam) => {
                let res = lam.apply(args);
                Self::at_base(res, espan)
            }
            _ => Expr::app(func.clone(), args.into()).at_opt(espan),
        }
    }
}

impl TypeFolder for Normalizer<'_, '_, '_> {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        let expr = expr.super_fold_with(self);
        let span = expr.span();
        match expr.kind() {
            ExprKind::App(func, args) => self.app(func, args, span),
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
