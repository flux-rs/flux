use std::ops::ControlFlow;

use itertools::Itertools;
use rustc_data_structures::{
    fx::FxIndexSet,
    graph::{DirectedGraph, Successors, scc::Sccs},
    unord::UnordMap,
};
use rustc_hir::def_id::{CrateNum, DefIndex, LOCAL_CRATE};
use rustc_macros::{TyDecodable, TyEncodable};

use super::{ESpan, fold::TypeSuperFoldable};
use crate::{
    def_id::{FluxDefId, FluxId, FluxLocalDefId},
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
    defns: UnordMap<FluxId<DefIndex>, NormalizeInfo>,
}

impl Default for NormalizedDefns {
    fn default() -> Self {
        Self { krate: LOCAL_CRATE, defns: UnordMap::default() }
    }
}

/// This type represents what we know about a flux-def *after*
/// normalization, i.e. after "inlining" all or some transitively
/// called flux-defs.
/// - When `FLUX_SMT_DEFINE_FUN=1` is set we inline
///   all *polymorphic* flux-defs, since they cannot
///   be represented  as `define-fun` in SMTLIB but leave
///   all *monomorphic* flux-defs un-inlined.
/// - When the above flag is not set, we replace *every* flux-def
///   with its (transitively) inlined body
#[derive(Clone, TyEncodable, TyDecodable)]
pub struct NormalizeInfo {
    /// the actual definition, with the `Binder` representing the parameters
    pub body: Binder<Expr>,
    /// whether or not this function is inlined (i.e. NOT represented as `define-fun`)
    pub inline: bool,
    /// the rank of this defn in the topological sort of all the flux-defs, needed so
    /// we can specify the `define-fun` in the correct order, without any "forward"
    /// dependencies which the SMT solver cannot handle
    pub rank: usize,
    /// whether or not this function is uninterpreted by default
    pub hide: bool,
}

pub(super) struct Normalizer<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    defs: Option<&'a UnordMap<FluxLocalDefId, NormalizeInfo>>,
}

impl NormalizedDefns {
    pub fn new(
        genv: GlobalEnv,
        defns: &[(FluxLocalDefId, Binder<Expr>, bool)],
    ) -> Result<Self, Vec<FluxLocalDefId>> {
        // 1. Topologically sort the Defns
        let ds = toposort(defns)?;

        // 2. Expand each defn in the sorted order
        let mut normalized = UnordMap::default();
        let mut ids = vec![];
        for (rank, i) in ds.iter().enumerate() {
            let (id, body, hide) = &defns[*i];
            let body = body.fold_with(&mut Normalizer::new(genv, Some(&normalized)));

            let inline = genv.should_inline_fun(id.to_def_id());
            let info = NormalizeInfo { body: body.clone(), inline, rank, hide: *hide };
            ids.push(*id);
            normalized.insert(*id, info);
        }
        Ok(Self {
            krate: LOCAL_CRATE,
            defns: normalized
                .into_items()
                .map(|(id, body)| (id.local_def_index(), body))
                .collect(),
        })
    }

    pub fn func_info(&self, did: FluxDefId) -> NormalizeInfo {
        debug_assert_eq!(self.krate, did.krate());
        self.defns.get(&did.index()).unwrap().clone()
    }
}

/// Simple graph structure for dependency analysis
struct DepGraph {
    successors: Vec<Vec<usize>>,
}

impl DirectedGraph for DepGraph {
    type Node = usize;

    fn num_nodes(&self) -> usize {
        self.successors.len()
    }
}

impl Successors for DepGraph {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.successors[node].iter().copied()
    }
}

/// Returns a vec<vec<usize>> representing the topological sort of the given
/// definitions based on their dependencies, i.e. a vector of SCCs, where
///    forall i < j, SCC_i does not depend on (i.e. "call") SCC_j
///    forall i, SCC_i is a vector of mutually
/// SCC comes befoIf there are no cycles,
/// * either Ok(d1...dn) which are topologically sorted such that
///   forall i < j, di does not depend on i.e. "call" dj
/// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1
fn toposort<T>(defns: &[(FluxLocalDefId, Binder<Expr>, T)]) -> Vec<Vec<usize>> {
    // 1. Make a Symbol to Index map
    let s2i: UnordMap<FluxLocalDefId, usize> = defns
        .iter()
        .enumerate()
        .map(|(i, defn)| (defn.0, i))
        .collect();

    // 2. Make the dependency graph (transposed: edges go from dependency to dependent)
    let mut successors = vec![Vec::new(); defns.len()];
    for (i, defn) in defns.iter().enumerate() {
        let deps = local_deps(&defn.1);
        for dep in deps {
            if let Some(&dep_idx) = s2i.get(&dep) {
                // Add edge from dependency to dependent (transposed)
                successors[dep_idx].push(i);
            }
        }
    }
    let graph = DepGraph { successors };

    // 3. Compute SCCs using rustc's algorithm
    let sccs = Sccs::new(&graph);

    // 4. Check for cycles: any SCC with more than one node indicates a cycle
    for scc_idx in sccs.all_sccs() {
        let nodes = sccs.nodes_in_scc(scc_idx);
        if nodes.len() > 1 {
            // Found a cycle
            return Err(nodes.iter().map(|&i| defns[i].0).collect());
        }
        // Check for self-loops
        if nodes.len() == 1 {
            let node = nodes[0];
            if graph.successors[node].contains(&node) {
                return Err(vec![defns[node].0]);
            }
        }
    }

    // 5. Return nodes in topological order (SCCs are already in reverse postorder)
    let mut result = Vec::with_capacity(defns.len());
    for scc_idx in sccs.all_sccs() {
        result.extend(sccs.nodes_in_scc(scc_idx));
    }
    Ok(result)
}

pub fn local_deps(body: &Binder<Expr>) -> FxIndexSet<FluxLocalDefId> {
    struct DepsVisitor(FxIndexSet<FluxLocalDefId>);
    impl TypeVisitor for DepsVisitor {
        #[allow(clippy::disallowed_methods, reason = "refinement functions cannot be extern specs")]
        fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
            if let ExprKind::App(func, ..) = expr.kind()
                && let ExprKind::GlobalFunc(SpecFuncKind::Def(did)) = func.kind()
                && let Some(did) = did.as_local()
            {
                self.0.insert(did);
            }
            expr.super_visit_with(self)
        }
    }
    let mut visitor = DepsVisitor(Default::default());
    let _ = body.visit_with(&mut visitor);
    visitor.0
}

impl<'a, 'genv, 'tcx> Normalizer<'a, 'genv, 'tcx> {
    pub(super) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        defs: Option<&'a UnordMap<FluxLocalDefId, NormalizeInfo>>,
    ) -> Self {
        Self { genv, defs }
    }

    #[allow(clippy::disallowed_methods, reason = "refinement functions cannot be extern specs")]
    fn func_defn(&self, did: FluxDefId) -> Binder<Expr> {
        if let Some(defs) = self.defs
            && let Some(local_id) = did.as_local()
        {
            defs.get(&local_id).unwrap().body.clone()
        } else {
            self.genv.normalized_info(did).body
        }
    }

    #[allow(clippy::disallowed_methods, reason = "refinement functions cannot be extern specs")]
    fn inline(&self, did: &FluxDefId) -> bool {
        let info = if let Some(defs) = self.defs
            && let Some(local_id) = did.as_local()
            && let Some(info) = defs.get(&local_id)
        {
            info
        } else {
            &self.genv.normalized_info(*did)
        };
        info.inline && !info.hide
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
            ExprKind::GlobalFunc(SpecFuncKind::Def(did)) if self.inline(did) => {
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
