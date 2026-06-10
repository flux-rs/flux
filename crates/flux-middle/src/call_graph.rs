//! Data types for the no-panic call graph.
//!
//! The graph is *constructed* by the `flux-opt` crate (the `call_graph` query provider) but the
//! types live here so they can be cached in `flux-middle` and consumed by both `flux-opt`
//! (no-panic inference) and `flux-refineck` (the checker, which recovers the resolved callee at a
//! call site by location).

use std::fmt;

use rustc_data_structures::{fx::FxIndexMap, unord::UnordMap};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::Location,
    ty::{GenericArgs, Instance, TyCtxt},
};

/// A single call site observed in a function's MIR body.
#[derive(Debug, Clone)]
pub struct CallSite<'tcx> {
    pub location: Location,
    pub kind: CallSiteKind<'tcx>,
}

#[derive(Debug, Clone)]
pub enum CallSiteKind<'tcx> {
    /// `Call` terminator that resolved to a concrete `Instance`
    /// (potentionally monomorphized)
    Resolved { callee: Instance<'tcx> },
    /// Synthetic edge from an `Assert` terminator with a reachable unwind path —
    /// represents the implicit call to `core::panicking::panic`.
    SynthesizedPanic,
    /// `Call` terminator on a `FnDef` where `Instance::try_resolve` failed.
    Unresolved { def_id: DefId },
    /// `Call` terminator on a non-`FnDef` type (function pointer, closure).
    DynamicDispatch,
}

/// A node in the call graph: an `Instance` together with its classification and, when it has an
/// analyzable body, the call sites observed in it.
#[derive(Debug, Clone)]
pub enum Node<'tcx> {
    /// MIR was available and walked. `is_mono` is true when the instance is a concrete
    /// monomorphization (args differ from the identity args), false for the source-level item.
    /// `call_sites` are the Call/Assert terminators observed in the body.
    Analyzed { is_mono: bool, call_sites: Vec<CallSite<'tcx>> },
    /// External crate function — panic spec looked up from crate metadata.
    ExternalCrate,
    /// Function with no analyzable body (no Rust body by design, MIR unavailable,
    /// or a non-`Item` instance such as a shim or virtual dispatch stub).
    /// Conservatively treated as `MightPanic`.
    Leaf(DefKind),
}

impl<'tcx> Node<'tcx> {
    /// Call sites observed in this node's body. Empty for non-`Analyzed` nodes.
    pub fn call_sites(&self) -> &[CallSite<'tcx>] {
        match self {
            Node::Analyzed { call_sites, .. } => call_sites,
            Node::ExternalCrate | Node::Leaf(_) => &[],
        }
    }
}

pub struct CallGraph<'tcx> {
    pub nodes: FxIndexMap<Instance<'tcx>, Node<'tcx>>,
    pub callers: UnordMap<Instance<'tcx>, Vec<Instance<'tcx>>>,
}

impl<'tcx> CallGraph<'tcx> {
    /// Builds a `CallGraph` from its nodes, deriving the `callers` map.
    pub fn new(nodes: FxIndexMap<Instance<'tcx>, Node<'tcx>>) -> Self {
        let mut graph = CallGraph { nodes, callers: UnordMap::default() };
        graph.build_callers();
        graph
    }

    fn build_callers(&mut self) {
        for (&caller, node) in &self.nodes {
            for callee in resolved_callees(node.call_sites()) {
                self.callers.entry(callee).or_default().push(caller);
            }
        }
    }

    /// The callee `Instance` resolved for the `Call` terminator at `location` in the body of
    /// `def_id`. The checker only ever checks identity bodies (mono instances of a local generic
    /// share the same `def_id` and body), so we look up the identity instance's node and scan its
    /// call sites. Returns `None` for call sites that did not resolve to a concrete instance
    /// (unresolved trait calls, dynamic dispatch) or whose body is not in the graph.
    pub fn resolved_callee(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        location: Location,
    ) -> Option<Instance<'tcx>> {
        let instance = Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id));
        let node = self.nodes.get(&instance)?;
        node.call_sites().iter().find_map(|site| {
            match site.kind {
                CallSiteKind::Resolved { callee } if site.location == location => Some(callee),
                _ => None,
            }
        })
    }
}

pub fn resolved_callees<'tcx>(
    call_sites: &[CallSite<'tcx>],
) -> impl Iterator<Item = Instance<'tcx>> {
    call_sites.iter().filter_map(|site| {
        match site.kind {
            CallSiteKind::Resolved { callee } => Some(callee),
            _ => None,
        }
    })
}

impl<'tcx> fmt::Display for Node<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Analyzed { is_mono, .. } => {
                if *is_mono {
                    write!(f, "Analyzed(mono)")
                } else {
                    write!(f, "Analyzed")
                }
            }
            Node::ExternalCrate => write!(f, "ExternalCrate"),
            Node::Leaf(kind) => write!(f, "Leaf({kind:?})"),
        }
    }
}

impl<'tcx> fmt::Display for CallSiteKind<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CallSiteKind::Resolved { callee } => write!(f, "-> {callee}"),
            CallSiteKind::SynthesizedPanic => write!(f, "-> panic"),
            CallSiteKind::Unresolved { def_id: method } => write!(f, "-> trait {method:?}"),
            CallSiteKind::DynamicDispatch => write!(f, "-> <dynamic>"),
        }
    }
}

impl<'tcx> fmt::Display for CallGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "call graph ({} nodes):", self.nodes.len())?;
        let mut nodes: Vec<_> = self.nodes.iter().collect();
        nodes.sort_by_key(|(inst, _)| format!("{inst}"));
        for (instance, node) in nodes {
            writeln!(f, "  {instance} [{node}]:")?;
            for site in node.call_sites() {
                writeln!(f, "    {} at {:?}", site.kind, site.location)?;
            }
        }
        Ok(())
    }
}
