use std::collections::{HashSet, VecDeque};

use rustc_hir::def_id::DefId;

use crate::CallGraph;

pub fn reachable_from_roots(call_graph: &CallGraph, roots: &[DefId]) -> HashSet<DefId> {
    let mut visited: HashSet<DefId> = HashSet::default();
    let mut worklist: VecDeque<DefId> = VecDeque::new();

    for root in roots {
        worklist.push_back(*root);
    }

    while let Some(f) = worklist.pop_front() {
        if !visited.insert(f) {
            continue;
        }

        if let Some(callees) = call_graph.get(&f) {
            for callee in callees {
                worklist.push_back(*callee);
            }
        }
    }

    visited.into_iter().collect()
}
