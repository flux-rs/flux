//! Data types for the no-panic call graph.
//!
//! The graph is *constructed* by the `flux-opt` crate (the `call_graph` query provider) but the
//! types live here so they can be cached in `flux-middle` and consumed by both `flux-opt`
//! (no-panic inference) and `flux-refineck` (the checker, which recovers the resolved callee at a
//! call site by location).

use std::fmt;

use rustc_data_structures::{fx::FxIndexMap, unord::UnordMap};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::Location,
    ty::{GenericArgs, Instance, InstanceKind, TyCtxt, TypeVisitableExt},
};

/// Identity of a call-graph node. Distinguishes an item *as defined in source* from a
/// *monomorphization* synthesized while building the graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum NodeKey<'tcx> {
    /// An item as written in source (generic or not), identified by its `DefId`.
    Item(DefId),
    /// A generic item monomorphized at concrete type/const args while building the
    /// call graph (e.g. `Vec::<i32>::push`). We must guarantee that the instance is fully
    /// monomorphic, i.e., the `Instance`'s args are all concrete types/consts.
    ///
    /// Use `NodeKey::from_instance` to classify an `Instance` into a `NodeKey`.
    Mono(Instance<'tcx>),
}

impl<'tcx> NodeKey<'tcx> {
    /// Classifies an `Instance` into a `NodeKey`.
    pub fn from_instance(instance: Instance<'tcx>) -> Self {
        if let InstanceKind::Item(def_id) = instance.def
            // - If `has_param()` is true then the instance is not fully monomorphic
            // - If args is empty then is a non-generic item
            && (instance.args.has_param() || instance.args.is_empty())
        {
            NodeKey::Item(def_id)
        } else {
            NodeKey::Mono(instance)
        }
    }

    pub fn def_id(self) -> DefId {
        match self {
            NodeKey::Item(def_id) => def_id,
            NodeKey::Mono(instance) => instance.def_id(),
        }
    }

    /// The `Instance` this key denotes. For an [`Item`](NodeKey::Item) this rebuilds the identity
    /// instance; for a [`Mono`](NodeKey::Mono) it is the stored instance.
    pub fn instance(self, tcx: TyCtxt<'tcx>) -> Instance<'tcx> {
        match self {
            NodeKey::Item(def_id) => {
                Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id))
            }
            NodeKey::Mono(instance) => instance,
        }
    }
}

/// A single call site observed in a function's MIR body.
#[derive(Debug, Clone)]
pub struct CallSite<'tcx> {
    pub location: Location,
    pub kind: CallSiteKind<'tcx>,
}

#[derive(Debug, Clone)]
pub enum CallSiteKind<'tcx> {
    /// `Call` terminator that resolved to a concrete callee node (a source item or a
    /// monomorphization).
    Resolved { callee: NodeKey<'tcx> },
    /// Synthetic edge from an `Assert` terminator with a reachable unwind path —
    /// represents the implicit call to `core::panicking::panic`.
    SynthesizedPanic,
    /// `Call` terminator on a `FnDef` where `Instance::try_resolve` failed.
    Unresolved { def_id: DefId },
    /// `Call` terminator on a non-`FnDef` type (function pointer, closure).
    DynamicDispatch,
}

/// A node in the call graph. The node's provenance (source item vs monomorphization) is carried by
/// its [`NodeKey`]; the node itself only records, when it has an analyzable body, the call sites
/// observed in it.
#[derive(Debug, Clone)]
pub enum Node<'tcx> {
    /// MIR was available and walked. `call_sites` are the Call/Assert terminators observed.
    Analyzed { call_sites: Vec<CallSite<'tcx>> },
    /// External crate function — panic spec looked up from crate metadata.
    ExternalCrate,
    /// Function with no analyzable body (no Rust body by design, MIR unavailable,
    /// or a non-`Item` instance such as a shim or virtual dispatch stub).
    /// Conservatively treated as `MightPanic`.
    Leaf(DefKind),
}

impl<'tcx> Node<'tcx> {
    /// Call sites observed in this node's body. Empty for non-`Analyzed` nodes.
    fn call_sites(&self) -> &[CallSite<'tcx>] {
        match self {
            Node::Analyzed { call_sites } => call_sites,
            Node::ExternalCrate | Node::Leaf(_) => &[],
        }
    }

    /// The callee nodes of this node's resolved call sites (skipping unresolved/dynamic ones).
    pub fn resolved_callees(&self) -> impl Iterator<Item = NodeKey<'tcx>> {
        self.call_sites().iter().filter_map(|site| {
            match site.kind {
                CallSiteKind::Resolved { callee } => Some(callee),
                _ => None,
            }
        })
    }
}

pub struct CallGraph<'tcx> {
    pub nodes: FxIndexMap<NodeKey<'tcx>, Node<'tcx>>,
    pub callers: UnordMap<NodeKey<'tcx>, Vec<NodeKey<'tcx>>>,
}

impl<'tcx> CallGraph<'tcx> {
    pub fn new(nodes: FxIndexMap<NodeKey<'tcx>, Node<'tcx>>) -> Self {
        let mut callers: UnordMap<_, Vec<_>> = UnordMap::default();
        for (&caller, node) in &nodes {
            for callee in node.resolved_callees() {
                callers.entry(callee).or_default().push(caller);
            }
        }
        CallGraph { nodes, callers }
    }

    /// The callee node resolved for the `Call` terminator at `location` in the body of `caller`.
    /// Returns `None` for call sites that did not resolve to a concrete node (unresolved trait
    /// calls, dynamic dispatch) or whose body is not in the graph.
    pub fn resolved_callee(&self, caller: DefId, location: Location) -> Option<NodeKey<'tcx>> {
        let node = self.nodes.get(&NodeKey::Item(caller))?;
        node.call_sites().iter().find_map(|site| {
            match site.kind {
                CallSiteKind::Resolved { callee } if site.location == location => Some(callee),
                _ => None,
            }
        })
    }
}

impl<'tcx> fmt::Display for NodeKey<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKey::Item(def_id) => write!(f, "{def_id:?}"),
            NodeKey::Mono(instance) => write!(f, "{instance}"),
        }
    }
}

impl<'tcx> fmt::Display for Node<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Analyzed { .. } => write!(f, "Analyzed"),
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
        nodes.sort_by_key(|(key, _)| format!("{key}"));
        for (key, node) in nodes {
            writeln!(f, "  {key} [{node}]:")?;
            for site in node.call_sites() {
                writeln!(f, "    {} at {:?}", site.kind, site.location)?;
            }
        }
        Ok(())
    }
}
