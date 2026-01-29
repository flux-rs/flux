use std::collections::HashSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::{CallGraph, CannotResolveReason, PanicReason, PanicSpec};

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn spec_to_color(spec: Option<&PanicSpec>) -> (&'static str, &'static str) {
    match spec {
        Some(PanicSpec::WillNotPanic) => ("green", "solid"),
        Some(PanicSpec::MightPanic(reason)) => {
            match reason {
                PanicReason::ContainsPanic => ("red", "bold"),
                PanicReason::Transitive(_) => ("yellow", "bold"),
                PanicReason::CallsTraitMethod(_) => ("blue", "dashed"),
                PanicReason::CallsMethodForNoMIR(_) => ("blue", "dashed"),
                PanicReason::CannotResolve(_) => ("orange", "dotted"),
                PanicReason::Unknown => panic!("This should never happen."),
            }
        }
        None => unreachable!(),
    }
}

pub fn emit_dot(
    tcx: TyCtxt,
    call_graph: &CallGraph,
    panic_specs: &FxHashMap<DefId, PanicSpec>,
) -> String {
    let mut reason_to_count = FxHashMap::default();
    for (_, reason) in panic_specs.iter() {
        let key = match reason {
            PanicSpec::WillNotPanic => "WillNotPanic".to_string(),
            PanicSpec::MightPanic(r) => {
                match r {
                    PanicReason::Unknown => "Unknown".to_string(),
                    PanicReason::ContainsPanic => "ContainsPanic".to_string(),
                    PanicReason::Transitive(_) => "Transitive".to_string(),
                    PanicReason::CallsTraitMethod(_) => "CallsTraitMethod".to_string(),
                    PanicReason::CallsMethodForNoMIR(_) => "CallsMethodForNoMIR".to_string(),
                    PanicReason::CannotResolve(r) => {
                        match r {
                            CannotResolveReason::UnresolvedTraitMethod(_) => {
                                "CannotResolve:UnresolvedTraitMethod".to_string()
                            }
                            CannotResolveReason::NotFnDef(_) => {
                                "CannotResolve:NotFnDef".to_string()
                            }
                        }
                    }
                }
            }
        };

        *reason_to_count.entry(key).or_insert(0) += 1;
    }

    println!("Callgraph panic analysis summary:");
    for (reason, count) in reason_to_count.iter() {
        println!("  {:<20} {}", reason, count);
    }

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
        let (color, style) = match panic_specs.get(&node) {
            Some(spec) => spec_to_color(Some(spec)),
            None => {
                match tcx.def_kind(node) {
                    rustc_hir::def::DefKind::AssocFn => ("blue", "dashed"),
                    _ => ("gray", "dotted"),
                }
            }
        };
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
