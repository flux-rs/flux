use std::collections::HashSet;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::{CallGraph, visualize::dot::emit_dot};

mod dot;
mod reachability;
mod roots;

use reachability::reachable_from_roots;
use roots::get_roots;

pub fn visualize(
    tcx: &TyCtxt,
    call_graph: CallGraph,
    filename: &str,
    fn_to_no_panic: &FxHashMap<DefId, super::PanicSpec>,
) {
    let def_ids: Vec<DefId> = call_graph.keys().copied().collect();
    let roots = get_roots(tcx, &def_ids, filename);
    let reachable = reachable_from_roots(&call_graph, &roots);
    let pruned_graph: CallGraph = call_graph
        .into_iter()
        .filter(|(f, _)| reachable.contains(f))
        .map(|(f, callees)| {
            let mut seen = HashSet::new();
            let mut filtered_callees = Vec::new();
            for callee in callees {
                if reachable.contains(&callee) && seen.insert(callee) {
                    filtered_callees.push(callee);
                }
            }
            (f, filtered_callees)
        })
        .collect();

    let dot = emit_dot(*tcx, &pruned_graph, fn_to_no_panic);

    // write to "filename-callgraph.dot"
    let out_filename = format!("{}-callgraph.dot", filename);
    std::fs::write(&out_filename, dot).expect("unable to write callgraph dot file");
    println!("Wrote callgraph to {}", out_filename);
}
