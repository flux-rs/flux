use std::collections::HashSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::{CallGraph, PanicReason, PanicSpec};

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn spec_to_color(spec: Option<&PanicSpec>) -> (&'static str, &'static str) {
    match spec {
        Some(PanicSpec::WillNotPanic) => ("green", "solid"),
        Some(PanicSpec::MightPanic(reason)) => {
            match reason {
                PanicReason::Transitive(_) => ("orange", "bold"),
                PanicReason::CallsTraitMethod(_) => ("blue", "dashed"),
                PanicReason::CallsMethodForNoMIR(_) => ("orange", "dashed"),
                PanicReason::Unknown => panic!("asldkjf"),
            }
        }
        None => ("gray", "dotted"),
    }
}

pub fn emit_dot(
    tcx: TyCtxt,
    call_graph: &CallGraph,
    panic_specs: &FxHashMap<DefId, PanicSpec>,
) -> String {
    let mut out = String::new();

    // Header
    out.push_str("digraph callgraph {\n");
    out.push_str("  rankdir=LR;\n");
    out.push_str("  node [shape=box, fontname=\"Helvetica\"];\n\n");

    // ---- Nodes ----
    let mut added_nodes: FxHashSet<DefId> = FxHashSet::default();

    for (caller, callees) in call_graph {
        added_nodes.insert(*caller);
        for callee in callees {
            added_nodes.insert(*callee);
        }
    }

    for node in added_nodes {
        let name = tcx.def_path_str(node);
        let spec = panic_specs.get(&node);
        let (color, style) = spec_to_color(spec);
        out.push_str(&format!("  \"{}\" [color={}, style={}];\n", escape(&name), color, style));
    }

    out.push('\n');

    // ---- Edges ----
    let mut seen = FxHashSet::default();

    for (caller, callees) in call_graph {
        let caller_label = tcx.def_path_str(*caller);

        for callee in callees {
            if !seen.insert((*caller, *callee)) {
                continue;
            }

            let callee_label = tcx.def_path_str(*callee);

            out.push_str(&format!(
                "  \"{}\" -> \"{}\";\n",
                escape(&caller_label),
                escape(&callee_label),
            ));
        }
    }

    out.push_str("}\n");
    out
}
