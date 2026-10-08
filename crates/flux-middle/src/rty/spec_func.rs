use std::ops::ControlFlow;

use itertools::Itertools;
use rustc_data_structures::{
    fx::{FxIndexMap, FxIndexSet},
    unord::UnordMap,
};
use rustc_hir::def_id::DefIndex;
use rustc_macros::{TyDecodable, TyEncodable};
use toposort_scc::IndexGraph;

use crate::{
    def_id::{FluxDefId, FluxId, FluxLocalDefId},
    rty::{
        Binder, Expr, ExprKind,
        expr::SpecFuncKind,
        fold::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
};

/// A spec function (aka flux-def) as written by the user, i.e., *before* inlining any of the
/// functions it calls.
#[derive(Clone, TyEncodable, TyDecodable)]
pub enum SpecFunc {
    /// An uninterpreted function
    Uif,
    /// A function with a body
    Defined {
        body: Binder<Expr>,
        /// Whether the function is uninterpreted by default
        hide: bool,
    },
}

impl SpecFunc {
    pub fn is_uif(&self) -> bool {
        matches!(self, SpecFunc::Uif)
    }
}

/// All the spec functions of a crate sorted topologically, i.e., every function comes after all
/// the functions (in the same crate) it calls.
///
/// Functions are identified by their index within the crate. Use [`GlobalEnv::spec_funcs`] to
/// get the spec functions of the crate a [`FluxDefId`] belongs to.
///
/// [`GlobalEnv::spec_funcs`]: crate::global_env::GlobalEnv::spec_funcs
#[derive(Default, TyEncodable, TyDecodable)]
pub struct SpecFuncs {
    funcs: FxIndexMap<FluxId<DefIndex>, SpecFunc>,
}

impl SpecFuncs {
    /// Sorts the spec functions of the local crate topologically. Returns `Err(cycle)` if there's
    /// a cycle in the functions.
    pub fn new(funcs: Vec<(FluxLocalDefId, SpecFunc)>) -> Result<Self, Vec<FluxLocalDefId>> {
        let order = toposort(&funcs)?;
        let mut funcs = funcs.into_iter().map(Some).collect_vec();
        let funcs = order
            .into_iter()
            .map(|i| {
                let (id, func) = funcs[i].take().unwrap();
                (id.local_def_index(), func)
            })
            .collect();
        Ok(Self { funcs })
    }

    pub fn get(&self, id: FluxId<DefIndex>) -> &SpecFunc {
        &self.funcs[&id]
    }

    /// The position of the function in the topological order. A function can only call functions
    /// in the same crate with a lower rank.
    pub fn rank(&self, id: FluxId<DefIndex>) -> usize {
        self.funcs.get_index_of(&id).unwrap()
    }
}

/// Returns
/// * either Ok(d1...dn) which are topologically sorted such that
///   forall i < j, di does not depend on i.e. "call" dj
/// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1
fn toposort(funcs: &[(FluxLocalDefId, SpecFunc)]) -> Result<Vec<usize>, Vec<FluxLocalDefId>> {
    // 1. Make a Symbol to Index map
    let s2i: UnordMap<FluxDefId, usize> = funcs
        .iter()
        .enumerate()
        .map(|(i, (id, _))| (id.to_def_id(), i))
        .collect();

    // 2. Make the dependency graph. Calls to functions in other crates are not in `s2i`.
    let mut adj_list = Vec::with_capacity(funcs.len());
    for (_, func) in funcs {
        if let SpecFunc::Defined { body, .. } = func {
            let deps = deps(body)
                .iter()
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
            Err(cycle.iter().map(|i| funcs[*i].0).collect())
        }
    }
}

/// Returns all the spec functions (of any crate) called in `body`
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
