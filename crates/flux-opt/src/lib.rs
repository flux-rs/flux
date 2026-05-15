#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

use flux_middle::{
    CannotResolveReason, PanicReason, PanicSpec, global_env::GlobalEnv, queries::Providers,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LOCAL_CRATE, LocalDefId},
    lang_items::LangItem,
};
use rustc_middle::{
    mir::{Location, TerminatorKind, UnwindAction},
    ty::{EarlyBinder, GenericArgs, Instance, InstanceKind, TyCtxt, TypeVisitableExt, TypingEnv},
};

pub fn provide(providers: &mut Providers) {
    providers.inferred_no_panic = inferred_no_panic;
}

pub fn inferred_no_panic(genv: GlobalEnv) -> FxHashMap<DefId, PanicSpec> {
    infer_no_panics(genv, |def_id| genv.inferred_no_panic(def_id))
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

// ---- Call graph types -------------------------------------------------------

/// A single call site observed in a function's MIR body.
#[derive(Debug, Clone)]
struct CallSite<'tcx> {
    location: Location,
    kind: CallSiteKind<'tcx>,
}

#[derive(Debug, Clone)]
enum CallSiteKind<'tcx> {
    /// `Call` terminator that resolved to a concrete `Instance`.
    Direct { callee: Instance<'tcx> },
    /// Synthetic edge from an `Assert` terminator with a reachable unwind path —
    /// represents the implicit call to `core::panicking::panic`.
    SynthesizedPanic { callee: Instance<'tcx> },
    /// `Call` terminator on a `FnDef` where `Instance::try_resolve` failed.
    UnresolvedTrait { method: DefId },
    /// `Call` terminator on a non-`FnDef` type (function pointer, closure).
    DynamicDispatch,
}

/// Classification of a node in the call graph.
#[derive(Debug, Clone)]
enum NodeKind {
    /// MIR was available and walked (local functions, stdlib, cstore-absent crates).
    Analyzed,
    /// Function with no Rust body by design (e.g. `extern "C"`, intrinsics).
    NoBody(DefKind),
    /// Function that should have a body but whose MIR could not be loaded.
    MIRUnavailable(DefKind),
    /// External crate function — panic spec looked up from crate metadata.
    ExternalCrate,
    /// Non-`Item` MIR instance (shim, virtual dispatch stub) or instance with
    /// abstract type/const params. Conservatively assumed `WillNotPanic`.
    Opaque,
}

#[derive(Debug, Clone)]
struct NodeInfo<'tcx> {
    kind: NodeKind,
    /// Call sites observed in this function's MIR body. Non-empty only for
    /// `NodeKind::Analyzed` nodes.
    call_sites: Vec<CallSite<'tcx>>,
}

struct LabeledCallGraph<'tcx> {
    nodes: FxHashMap<Instance<'tcx>, NodeInfo<'tcx>>,
    /// Identity instances of local root functions — the only nodes that appear
    /// in the final `FxHashMap<DefId, PanicSpec>` output.
    roots: FxHashSet<Instance<'tcx>>,
}

// ---- Entry points -----------------------------------------------------------

/// The entry point for no-panic inference. Given a root function, explores its
/// call graph and returns an over-approximation of whether it might panic.
pub fn infer_no_panics(
    genv: GlobalEnv,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> FxHashMap<DefId, PanicSpec> {
    let graph = build_call_graph(genv);
    run_fixpoint(&graph, external_spec)
}

// ---- Build phase ------------------------------------------------------------

fn build_call_graph<'tcx>(genv: GlobalEnv<'_, 'tcx>) -> LabeledCallGraph<'tcx> {
    let tcx = genv.tcx();

    // We need to use `iter_local_def_id` instead of `hir_body_owners`
    // so that we can visit trait items with no MIR.
    let roots: Vec<LocalDefId> = tcx
        .iter_local_def_id()
        .filter(|local_id| tcx.def_kind(local_id.to_def_id()).is_fn_like())
        .collect();

    explore(genv, &roots)
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
                                call_sites.push(CallSite {
                                    location,
                                    kind: CallSiteKind::Direct { callee: instance },
                                });
                            }
                            _ => {
                                call_sites.push(CallSite {
                                    location,
                                    kind: CallSiteKind::UnresolvedTrait {
                                        method: *callee_def_id,
                                    },
                                });
                            }
                        }
                    }
                    _ => {
                        call_sites.push(CallSite {
                            location,
                            kind: CallSiteKind::DynamicDispatch,
                        });
                    }
                }
            }
            TerminatorKind::Assert { unwind, .. }
                if !matches!(unwind, UnwindAction::Unreachable) =>
            {
                // An Assert with a reachable unwind path can panic without any explicit callee.
                // Synthesize a call to `core::panicking::panic` so the fixpoint sees the panic edge.
                if let Some(panic_def_id) = tcx.lang_items().get(LangItem::Panic) {
                    let panic_args = GenericArgs::identity_for_item(tcx, panic_def_id);
                    if let Ok(Some(instance)) =
                        Instance::try_resolve(tcx, typing_env, panic_def_id, panic_args)
                    {
                        call_sites.push(CallSite {
                            location,
                            kind: CallSiteKind::SynthesizedPanic { callee: instance },
                        });
                    }
                }
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

/// Call sites of an external instance. Uses `instance_mir` so that
/// `instantiate_mir_and_normalize_erasing_regions` can substitute the concrete
/// args carried by `instance` into the generic body.
fn extern_callees<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Vec<CallSite<'tcx>> {
    callees_in_body(tcx, instance, tcx.instance_mir(instance.def))
}

fn resolved_callees<'tcx>(call_sites: &[CallSite<'tcx>]) -> impl Iterator<Item = Instance<'tcx>> {
    call_sites.iter().filter_map(|site| match site.kind {
        CallSiteKind::Direct { callee } | CallSiteKind::SynthesizedPanic { callee } => {
            Some(callee)
        }
        _ => None,
    })
}

fn explore<'tcx>(genv: GlobalEnv<'_, 'tcx>, roots: &[LocalDefId]) -> LabeledCallGraph<'tcx> {
    let tcx = genv.tcx();
    let mut graph = LabeledCallGraph {
        nodes: FxHashMap::default(),
        roots: FxHashSet::default(),
    };
    // Instance-level worklist and visited set to handle the same DefId being
    // called with different concrete type args.
    let mut worklist: Vec<Instance<'_>> = Vec::new();
    let mut explored: FxHashSet<Instance<'_>> = FxHashSet::default();

    // Seed the worklist with the root functions.
    for &root_local in roots {
        let root_def_id = root_local.to_def_id();
        let root_instance =
            Instance::new_raw(root_def_id, GenericArgs::identity_for_item(tcx, root_def_id));

        if !tcx.is_mir_available(root_def_id) {
            let def_kind = tcx.def_kind(root_def_id);
            let kind = if matches!(def_kind, DefKind::AssocFn) {
                NodeKind::NoBody(def_kind)
            } else {
                NodeKind::MIRUnavailable(def_kind)
            };
            graph.nodes.insert(root_instance, NodeInfo { kind, call_sites: vec![] });
            graph.roots.insert(root_instance);
            continue;
        }

        let call_sites = local_callees(tcx, root_local);
        worklist.extend(resolved_callees(&call_sites));
        graph
            .nodes
            .insert(root_instance, NodeInfo { kind: NodeKind::Analyzed, call_sites });
        graph.roots.insert(root_instance);
    }

    while let Some(instance) = worklist.pop() {
        if explored.contains(&instance) {
            continue;
        }
        explored.insert(instance);

        let def_id = instance.def_id();

        // External non-stdlib callees: treat as a leaf and record for spec lookup.
        if !should_include_in_call_graph(genv, def_id.krate) {
            graph.nodes.entry(instance).or_insert(NodeInfo {
                kind: NodeKind::ExternalCrate,
                call_sites: vec![],
            });
            continue;
        }

        // Only Item instances have MIR we can walk; shims, intrinsics, and
        // virtual-dispatch stubs are treated as opaque WillNotPanic leaves.
        // If the instance still carries abstract type/const params, normalization
        // inside its body would panic — treat as opaque leaf.
        let has_abstract_args = instance.args.has_param();
        if matches!(instance.def, InstanceKind::Item(_))
            && tcx.is_mir_available(def_id)
            && !has_abstract_args
        {
            let call_sites = extern_callees(tcx, instance);
            worklist.extend(resolved_callees(&call_sites));
            // or_insert so the first concrete instantiation of an Instance wins;
            // subsequent identical instances still push their callees onto the worklist.
            graph
                .nodes
                .entry(instance)
                .or_insert(NodeInfo { kind: NodeKind::Analyzed, call_sites });
        } else if matches!(instance.def, InstanceKind::Item(_))
            && !tcx.is_mir_available(def_id)
            && !has_abstract_args
        {
            // Item with no MIR and concrete args (e.g. extern "C" or platform-specific
            // functions). Distinguish functions with no Rust body by design from those
            // whose MIR we simply cannot load. The exact heuristic is TBD; for now we
            // conservatively classify all such nodes as MIRUnavailable.
            let def_kind = tcx.def_kind(def_id);
            graph.nodes.entry(instance).or_insert(NodeInfo {
                kind: NodeKind::MIRUnavailable(def_kind),
                call_sites: vec![],
            });
        } else {
            // Non-Item instance (shim, intrinsic, virtual dispatch stub) or abstract args.
            graph
                .nodes
                .entry(instance)
                .or_insert(NodeInfo { kind: NodeKind::Opaque, call_sites: vec![] });
        }
    }

    graph
}

// ---- Fixpoint phase ---------------------------------------------------------

/// Consumes the labeled call graph and produces a `PanicSpec` for every root node.
///
/// Seeding is explicit per `NodeKind`:
/// - `ExternalCrate` → looked up via `external_spec`
/// - `Opaque`        → `WillNotPanic` (compiler-generated glue, conservatively safe)
/// - `NoBody` / `MIRUnavailable` → `MightPanic(CannotResolve(...))`
/// - `Analyzed` with unresolvable call sites → `MightPanic(CannotResolve(...))` (final)
/// - `Analyzed` with no unresolvable calls → `MightPanic(Unknown)`, resolved by fixpoint
fn run_fixpoint(
    graph: &LabeledCallGraph<'_>,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> FxHashMap<DefId, PanicSpec> {
    // --- Seeding ---
    let mut specs: FxHashMap<Instance<'_>, PanicSpec> = FxHashMap::default();

    for (&instance, node) in &graph.nodes {
        let def_id = instance.def_id();
        let spec = match &node.kind {
            NodeKind::ExternalCrate => external_spec(def_id),
            NodeKind::Opaque => PanicSpec::WillNotPanic,
            NodeKind::NoBody(def_kind) => {
                PanicSpec::MightPanic(PanicReason::CannotResolve(
                    CannotResolveReason::NoMIRAvailable(def_id, *def_kind),
                ))
            }
            NodeKind::MIRUnavailable(def_kind) => {
                PanicSpec::MightPanic(PanicReason::CannotResolve(
                    CannotResolveReason::NoMIRAvailable(def_id, *def_kind),
                ))
            }
            NodeKind::Analyzed => {
                // If any call site is statically unresolvable, the function is
                // immediately MightPanic(CannotResolve). Otherwise start as Unknown
                // for the fixpoint to resolve.
                let unresolvable = node.call_sites.iter().find(|site| {
                    matches!(
                        site.kind,
                        CallSiteKind::DynamicDispatch | CallSiteKind::UnresolvedTrait { .. }
                    )
                });
                if let Some(site) = unresolvable {
                    let reason = match site.kind {
                        CallSiteKind::DynamicDispatch => {
                            CannotResolveReason::NotFnDef(def_id)
                        }
                        CallSiteKind::UnresolvedTrait { method } => {
                            CannotResolveReason::UnresolvedTraitMethod(method)
                        }
                        _ => unreachable!(),
                    };
                    PanicSpec::MightPanic(PanicReason::CannotResolve(reason))
                } else {
                    PanicSpec::MightPanic(PanicReason::Unknown)
                }
            }
        };
        specs.insert(instance, spec);
    }

    // --- Fixpoint iteration ---
    let mut changed = true;
    while changed {
        changed = false;

        let instances: Vec<Instance<'_>> = graph.nodes.keys().copied().collect();

        for instance in instances {
            let current_spec = specs.get(&instance).unwrap();

            // CannotResolve and WillNotPanic are final states; skip them.
            match current_spec {
                PanicSpec::WillNotPanic
                | PanicSpec::MightPanic(PanicReason::CannotResolve(_)) => continue,
                _ => {}
            }

            let call_sites = &graph.nodes[&instance].call_sites;

            let bad_callees: Vec<Instance<'_>> = call_sites
                .iter()
                .filter_map(|site| match site.kind {
                    CallSiteKind::Direct { callee }
                    | CallSiteKind::SynthesizedPanic { callee } => {
                        match specs.get(&callee) {
                            Some(PanicSpec::WillNotPanic) => None,
                            _ => Some(callee),
                        }
                    }
                    // DynamicDispatch and UnresolvedTrait are handled at seeding time.
                    CallSiteKind::DynamicDispatch | CallSiteKind::UnresolvedTrait { .. } => None,
                })
                .collect();

            // Case 1: all callees are known to not panic.
            if bad_callees.is_empty() {
                changed = true;
                specs.insert(instance, PanicSpec::WillNotPanic);
            // Case 2: a callee transitively might panic.
            } else if matches!(current_spec, PanicSpec::MightPanic(PanicReason::Unknown)) {
                changed = true;
                specs.insert(instance, PanicSpec::MightPanic(PanicReason::Transitive));
            }
        }
    }

    // Filter to root instances only, mapping back to DefId.
    graph
        .roots
        .iter()
        .filter_map(|instance| {
            let spec = specs.get(instance)?;
            Some((instance.def_id(), spec.clone()))
        })
        .collect()
}
