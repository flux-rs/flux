use std::fmt;

use flux_middle::global_env::GlobalEnv;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_middle::{
    mir::{Location, TerminatorKind, UnwindAction},
    ty::{EarlyBinder, GenericArgs, Instance, InstanceKind, TyCtxt, TypeVisitableExt, TypingEnv},
};

// ---- Types ------------------------------------------------------------------

/// A single call site observed in a function's MIR body.
#[derive(Debug, Clone)]
pub(crate) struct CallSite<'tcx> {
    pub(crate) location: Location,
    pub(crate) kind: CallSiteKind<'tcx>,
}

#[derive(Debug, Clone)]
pub(crate) enum CallSiteKind<'tcx> {
    /// `Call` terminator that resolved to a concrete `Instance`.
    Resolved { callee: Instance<'tcx> },
    /// Synthetic edge from an `Assert` terminator with a reachable unwind path —
    /// represents the implicit call to `core::panicking::panic`.
    SynthesizedPanic,
    /// `Call` terminator on a `FnDef` where `Instance::try_resolve` failed.
    Unresolved { def_id: DefId },
    /// `Call` terminator on a non-`FnDef` type (function pointer, closure).
    DynamicDispatch,
}

/// Classification of a node in the call graph.
#[derive(Debug, Clone)]
pub(crate) enum NodeKind {
    /// MIR was available and walked.
    /// `is_mono` is true when the instance is a concrete monomorphization
    /// (args differ from the identity args). False for the source-level item.
    Analyzed { is_mono: bool },
    /// External crate function — panic spec looked up from crate metadata.
    ExternalCrate,
    /// Function with no analyzable body (no Rust body by design, MIR unavailable,
    /// or a non-`Item` instance such as a shim or virtual dispatch stub).
    /// Conservatively treated as `MightPanic`.
    Leaf(DefKind),
}

#[derive(Debug, Clone)]
pub(crate) struct NodeInfo<'tcx> {
    pub(crate) kind: NodeKind,
    /// Call sites observed in this function's MIR body. Non-empty only for
    /// `NodeKind::Analyzed` nodes.
    pub(crate) call_sites: Vec<CallSite<'tcx>>,
}

pub(crate) struct CallGraph<'tcx> {
    pub(crate) nodes: FxHashMap<Instance<'tcx>, NodeInfo<'tcx>>,
    pub(crate) callers: FxHashMap<Instance<'tcx>, Vec<Instance<'tcx>>>,
}

// ---- Display ----------------------------------------------------------------

impl fmt::Display for NodeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Analyzed { is_mono } => {
                if *is_mono {
                    write!(f, "Analyzed(mono)")
                } else {
                    write!(f, "Analyzed")
                }
            }
            NodeKind::ExternalCrate => write!(f, "ExternalCrate"),
            NodeKind::Leaf(kind) => write!(f, "Leaf({kind:?})"),
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
        for (instance, info) in nodes {
            writeln!(f, "  {instance} [{}]:", info.kind)?;
            for site in &info.call_sites {
                writeln!(f, "    {} at {:?}", site.kind, site.location)?;
            }
        }
        Ok(())
    }
}

// ---- Entry point ------------------------------------------------------------

pub(crate) fn build_call_graph<'tcx>(genv: GlobalEnv<'_, 'tcx>) -> CallGraph<'tcx> {
    let tcx = genv.tcx();

    // We need to use `iter_local_def_id` instead of `hir_body_owners`
    // so that we can visit trait items with no MIR.
    let roots: Vec<LocalDefId> = tcx
        .iter_local_def_id()
        .filter(|local_id| tcx.def_kind(local_id.to_def_id()).is_fn_like())
        .collect();

    let g = explore(genv, &roots);
    eprintln!("{g}");
    g
}

// ---- Helpers ----------------------------------------------------------------

fn is_method_in_trait<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let def_kind = tcx.def_kind(def_id);
    if matches!(def_kind, DefKind::AssocFn) {
        matches!(tcx.associated_item(def_id).container, rustc_middle::ty::AssocContainer::Trait)
    } else {
        false
    }
}

fn is_identity_instance<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> bool {
    let identity = GenericArgs::identity_for_item(tcx, instance.def_id());
    instance.args == identity
}

/// If `instance` is an `InstanceKind::Item` whose args still contain abstract type/const
/// parameters (i.e., we are inside a generic caller), normalize it to its identity instance so
/// all call sites for the same generic function fold into one graph node.
fn normalize_abstract_args<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Instance<'tcx> {
    if matches!(instance.def, InstanceKind::Item(_)) && instance.args.has_param() {
        let def_id = instance.def_id();
        Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id))
    } else {
        instance
    }
}

fn should_include_in_call_graph(genv: GlobalEnv, krate: CrateNum) -> bool {
    krate == LOCAL_CRATE || is_outside_cstore(genv, krate) || is_stdlib_crate(genv, krate)
}

fn is_stdlib_crate(genv: GlobalEnv, krate: CrateNum) -> bool {
    matches!(genv.tcx().crate_name(krate).as_str(), "core" | "alloc" | "std")
}

fn is_outside_cstore(genv: GlobalEnv, krate: CrateNum) -> bool {
    // If the crate has no Flux metadata in the cratestore, flux never visited it,
    // so we should include that crate's functions in this call graph.
    !genv.cstore_has_crate(krate)
}

/// Walks `body`'s Call and Assert terminators, returning all call sites found.
fn callees_in_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: Instance<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> Vec<CallSite<'tcx>> {
    let typing_env = TypingEnv::non_body_analysis(tcx, caller.def_id());
    let mut call_sites = Vec::new();

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let terminator = bb_data.terminator();
        let location = Location { block: bb, statement_index: bb_data.statements.len() };

        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let ty = func.ty(&body.local_decls, tcx);
                // Apply the caller's concrete type args to get the concrete callee type.
                let ty = caller.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    typing_env,
                    EarlyBinder::bind(ty),
                );

                match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(callee_def_id, callee_args) => {
                        match Instance::try_resolve(tcx, typing_env, *callee_def_id, callee_args) {
                            Ok(Some(instance)) => {
                                let instance = normalize_abstract_args(tcx, instance);
                                call_sites.push(CallSite {
                                    location,
                                    kind: CallSiteKind::Resolved { callee: instance },
                                });
                            }
                            _ => {
                                call_sites.push(CallSite {
                                    location,
                                    kind: CallSiteKind::Unresolved { def_id: *callee_def_id },
                                });
                            }
                        }
                    }
                    _ => {
                        call_sites.push(CallSite { location, kind: CallSiteKind::DynamicDispatch });
                    }
                }
            }
            TerminatorKind::Assert { unwind, .. }
                if !matches!(unwind, UnwindAction::Unreachable) =>
            {
                call_sites.push(CallSite { location, kind: CallSiteKind::SynthesizedPanic });
            }
            _ => {}
        }
    }

    call_sites
}

/// Call sites of a local function. Uses `optimized_mir` (regions erased) to
/// avoid region inference variables panicking inside
/// `instantiate_mir_and_normalize_erasing_regions`.
fn local_callees<'tcx>(tcx: TyCtxt<'tcx>, local_id: LocalDefId) -> Vec<CallSite<'tcx>> {
    let def_id = local_id.to_def_id();
    let caller = Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id));
    callees_in_body(tcx, caller, tcx.optimized_mir(def_id))
}

/// Call sites of a worklist instance. After normalization all non-mono instances on the worklist
/// are identity instances, so `instance_mir` returns the unspecialized body.
fn item_callees<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Vec<CallSite<'tcx>> {
    callees_in_body(tcx, instance, tcx.instance_mir(instance.def))
}

pub(crate) fn resolved_callees<'tcx>(
    call_sites: &[CallSite<'tcx>],
) -> impl Iterator<Item = Instance<'tcx>> {
    call_sites.iter().filter_map(|site| {
        match site.kind {
            CallSiteKind::Resolved { callee } => Some(callee),
            _ => None,
        }
    })
}

fn explore<'tcx>(genv: GlobalEnv<'_, 'tcx>, roots: &[LocalDefId]) -> CallGraph<'tcx> {
    let tcx = genv.tcx();
    let mut graph = CallGraph { nodes: FxHashMap::default(), callers: FxHashMap::default() };
    // Instance-level worklist and visited set to handle the same DefId being
    // called with different concrete type args.
    let mut worklist: Vec<Instance<'_>> = Vec::new();
    let mut explored: FxHashSet<Instance<'_>> = FxHashSet::default();

    // Seed the worklist with the root functions' callees.
    for &root_local in roots {
        let def_id = root_local.to_def_id();

        if is_method_in_trait(tcx, def_id) {
            continue;
        }

        let instance = Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id));
        let (node_kind, call_sites) = if tcx.is_mir_available(def_id) {
            (NodeKind::Analyzed { is_mono: false }, local_callees(tcx, root_local))
        } else {
            (NodeKind::Leaf(tcx.def_kind(def_id)), vec![])
        };
        for callee in resolved_callees(&call_sites) {
            worklist.push(callee);
            graph.callers.entry(callee).or_default().push(instance);
        }
        graph
            .nodes
            .insert(instance, NodeInfo { kind: node_kind, call_sites });
        explored.insert(instance);
    }

    while let Some(instance) = worklist.pop() {
        if explored.contains(&instance) {
            continue;
        }
        explored.insert(instance);

        let def_id = instance.def_id();

        // External non-stdlib callees: treat as a leaf and record for spec lookup.
        if !should_include_in_call_graph(genv, def_id.krate) {
            graph
                .nodes
                .entry(instance)
                .or_insert(NodeInfo { kind: NodeKind::ExternalCrate, call_sites: vec![] });
            continue;
        }

        if let InstanceKind::Item(_) = instance.def {
            if tcx.is_mir_available(def_id) {
                let call_sites = item_callees(tcx, instance);
                for callee in resolved_callees(&call_sites) {
                    worklist.push(callee);
                    graph.callers.entry(callee).or_default().push(instance);
                }
                let is_mono = !is_identity_instance(tcx, instance);
                graph
                    .nodes
                    .entry(instance)
                    .or_insert(NodeInfo { kind: NodeKind::Analyzed { is_mono }, call_sites });
            } else {
                graph.nodes.entry(instance).or_insert(NodeInfo {
                    kind: NodeKind::Leaf(tcx.def_kind(def_id)),
                    call_sites: vec![],
                });
            }
        } else {
            graph.nodes.entry(instance).or_insert(NodeInfo {
                kind: NodeKind::Leaf(tcx.def_kind(def_id)),
                call_sites: vec![],
            });
        }
    }

    graph
}
