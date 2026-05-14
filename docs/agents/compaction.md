Goal
Make the set of "non-cut" KVars identified by the Rust in-crate solver (rust-fixpoint) exactly match what the external Haskell fixpoint binary reports in its nonCutsSolution JSON field. The comparison happens in run_task_with_cache in fixpoint_encoding.rs under the rust-fixpoint feature flag.
Instructions
- Do NOT use xtask to build — it hangs. Build with:
    cargo build --bin flux-driver --features rust-fixpoint
  - Run individual tests with:
    FLUX_SYSROOT=/home/cole/research/flux/sysroot \
  FLUX_DRIVER=/home/cole/research/flux/target/debug/flux-driver \
  /home/cole/research/flux/target/debug/flux \
    --edition=2021 --crate-type=rlib <path-to-test.rs>
  - The primary failing test is tests/tests/pos/structs/dot01.rs; also failing: dot02.rs, bsearch.rs, bsearch1.rs
- Reference docs: docs/agents/compare_kvars.md and KVarElimination-Implementation.md
- The Haskell fixpoint source is at /home/cole/research/liquid-fixpoint/src/
Discoveries
The Correct Algorithm (Key Insight)
The Haskell fixpoint does SCC-based cut selection on a bipartite constraint-KVar graph, not simple leaf-peeling. The critical file is src/Language/Fixpoint/Graph/Deps.hs.
How the Haskell algorithm works:
1. Enumerate sub-constraints (each is a full ForAll* chain ending in a Pred/tag leaf). Each gets a unique ID.
2. Build bipartite edges: (KVar k, Cstr i) if k in LHS of i; (Cstr i, KVar k') if k' is head of i.
3. Compute SCCs of the bipartite graph using G.stronglyConnCompR.
4. For each SCC:
   - Singleton without self-loop → non-cut
   - Otherwise → cycle: apply edgeRankCut — pick the KVar with the lowest "rank" (= minimum fragment/sub-constraint index where that KVar appears as an LHS assumption) as the cut. Remove it, recompute SCCs of remaining nodes, recurse.
5. The edgeRankCut function: rank[k] = min sub-constraint ID where k appears in LHS.
Key equivalence: The SCCs of the KVar-only dependency graph (kvar_dep_graph) are the same node sets as the SCCs of the projected bipartite graph (SCCs are invariant under edge reversal and projection via path equivalence). So we can use the existing KVar-only dep_graph for SCC computation; we only need to add the rank-based cut selection.
Concrete Trace for dot01.rs
Fragments (DFS order from depth_first_fragments()):
- Frags 0, 1: lhs=[] → no rank updates
- Frags 2, 3, 4: lhs=k0, k1, k2, k3 → rankk2=rankk3=2
- Frags 5, 6, 7, 8: lhs=k0, k1 → rankk0=rankk1=2
- Frags 9, 10: lhs=k0, k1, k4, k5 → rankk4=rankk5=9
dep_graph SCCs: {k0, k1} and {k2, k3, k4, k5} (no path from k0/k1 to k2-k5).
For SCC {k2, k3, k4, k5}: k2/k3 have rank 2, k4/k5 have rank 9. Pick k2 as cut. Remaining SCC {k3, k4, k5} still has cycle → pick k3. Remaining {k4, k5} has empty deps → k4 and k5 are non-cuts ✓ (matches external fixpoint).
dep_graph Fix (Already Applied)
The ForAll arm of kvar_dep_graph now uses graph.entry(kvar.clone()).or_default() (registers assumption kvars as nodes with empty deps, not inheriting outer deps). The previous "fix" incorrectly used .extend(deps.iter().cloned()) which gave spurious deps to assumption kvars.
Previous Bug (Before This Session)
Before any fix, assumption-only kvars were not added to the graph at all, so the leaf-peeling loop never found them as non-cuts, producing empty rust: [] results.
Two Separate Issues
1. Fixed: Assumption kvars not appearing as graph nodes → fixed with or_default() (no dep inheritance)
2. Not yet fixed: The algorithm is leaf-peeling instead of SCC+rank → needs the new algorithm in compute_non_cuts
Accomplished
Completed
- ✅ Fixed kvar_dep_graph ForAll arm: assumption kvars registered with empty deps (or_default() only, no .extend(deps...))
- ✅ Added Constraint::kvar_ranks(n_max: usize) -> HashMap<T::KVar, usize> to constraint_solving.rs — computes min fragment index per kvar for LHS appearances
- ✅ Added temporary debug eprintln!("DEBUG constraint:\n{}", self.constraint) in lib.rs::rust_non_cuts and eprintln!("DEBUG dep_graph: ...") in constraint_with_env.rs::eliminate_acyclic_kvars — these should be removed before finishing
- ✅ Verified the dep_graph is now structurally correct (k4/k5 have non-empty deps because they ARE heads in some fragments, but that's correct — they're in a cycle with k2/k3)
- ✅ Confirmed the correct algorithm (SCC+rank) will produce non_cuts=[k4,k5] for dot01.rs
In Progress
- 🔄 NOT YET DONE: Rewrite compute_non_cuts in constraint_with_env.rs to use the SCC+rank (edgeRankCut) algorithm instead of calling eliminate_acyclic_kvars
Remaining Work
1. Implement the SCC+rank algorithm in compute_non_cuts (the main remaining task):
   - Compute rank via self.constraint.kvar_ranks(fragment_count)
   - Compute dep_graph via self.constraint.kvar_dep_graph()
   - Get SCCs via graph::topological_sort_sccs(&dep_graph)
   - For each SCC, apply scc_dep logic (singleton without self-loop → non-cut; otherwise cycle → pick min-rank KVar as cut, recurse on sub-graph)
2. Remove all debug eprintln! statements from lib.rs and constraint_with_env.rs
3. Run all failing tests to verify they pass
Pseudocode for the New compute_non_cuts
pub fn compute_non_cuts(&mut self) -> Vec<String> {
    use crate::Identifier;
    let n_max = self.constraint.depth_first_fragments().count();
    let rank = self.constraint.kvar_ranks(n_max);
    let dep_graph = self.constraint.kvar_dep_graph();
    let sccs = graph::topological_sort_sccs(&dep_graph);
    let mut non_cuts: Vec<T::KVar> = Vec::new();
    for scc in sccs {
        scc_dep(&scc, &dep_graph, &rank, n_max, &mut non_cuts);
    }
    non_cuts.into_iter().map(|k| format!("{}", k.display())).collect()
}
fn scc_dep<T: Types>(
    scc: &[T::KVar],
    dep_graph: &HashMap<T::KVar, Vec<T::KVar>>,
    rank: &HashMap<T::KVar, usize>,
    n_max: usize,
    non_cuts: &mut Vec<T::KVar>,
) {
    if scc.is_empty() { return; }
    if scc.len() == 1 {
        let k = &scc[0];
        let has_self_loop = dep_graph.get(k).map_or(false, |deps| deps.contains(k));
        if !has_self_loop {
            non_cuts.push(k.clone());
        }
        // else: singleton with self-loop → cut, do nothing
        return;
    }
    // Multi-node SCC: pick cut = kvar with minimum rank
    let cut = scc.iter()
        .min_by_key(|k| rank.get(*k).copied().unwrap_or(n_max))
        .unwrap()
        .clone();
    // Build sub-graph of remaining nodes
    let remaining: HashSet<T::KVar> = scc.iter().filter(|k| **k != cut).cloned().collect();
    let sub_graph: HashMap<T::KVar, Vec<T::KVar>> = remaining.iter()
        .map(|k| {
            let deps = dep_graph.get(k).map_or(vec![], |d| {
                d.iter().filter(|dep| remaining.contains(*dep)).cloned().collect()
            });
            (k.clone(), deps)
        })
        .collect();
    // Recompute SCCs on sub-graph and recurse
    for sub_scc in graph::topological_sort_sccs(&sub_graph) {
        scc_dep(&sub_scc, &sub_graph, rank, n_max, non_cuts);
    }
}
Note: scc_dep must be a free function (not a method), placed outside the impl<T: Types> ConstraintWithEnv<T> block, gated under #[cfg(feature = "rust-fixpoint")].
Relevant files / directories
Modified files
- lib/liquid-fixpoint/src/constraint_solving.rs — Added kvar_ranks() method; fixed kvar_dep_graph() ForAll arm (assumption kvars use or_default() with no dep inheritance); has temporary debug eprintln! in eliminate_acyclic_kvars → remove before done
- lib/liquid-fixpoint/src/constraint_with_env.rs — compute_non_cuts still uses old leaf-peeling via eliminate_acyclic_kvars → needs to be rewritten; has temporary debug eprintln! → remove; eliminate_acyclic_kvars returns Vec<T::KVar>
- lib/liquid-fixpoint/src/lib.rs — Has temporary eprintln!("DEBUG constraint: ...") in rust_non_cuts → remove; run_external() and rust_non_cuts() methods added
- crates/flux-infer/src/fixpoint_encoding.rs — run_task_with_cache() calls run_external() always; under #[cfg(feature = "rust-fixpoint")] compares sets and panics on mismatch
Key reference files (read-only)
- lib/liquid-fixpoint/src/graph.rs — topological_sort_sccs (public, returns Vec<Vec<T>>); find_sccs (private, Kosaraju's algorithm)
- lib/liquid-fixpoint/src/constraint_fragments.rs — ConstraintFragments iterator for DFS fragments
- /home/cole/research/liquid-fixpoint/src/Language/Fixpoint/Graph/Deps.hs — Ground-truth Haskell implementation of elimVars, sccElims, edgeRankCut, cycleDep
- tests/tests/pos/structs/dot01.rs — Primary failing test case
- KVarElimination-Implementation.md — Algorithm overview doc
▣  Compaction · Claude Sonnet 4.6 · 55.0s
Thinking: Let me review the current state of the codebase to understand what's been done and what needs to be done next. The summary says:
1. The main remaining task is to implement the SCC+rank algorithm in compute_non_cuts
2. Remove debug eprintln! statements
Let me look at the relevant files to understand the current state.
# Todos
[•] 
Implement SCC+rank algorithm in compute_non_cuts
[ ] 
Remove debug eprintln! statements from lib.rs, constraint_with_env.rs, constraint_solving.rs
[ ] 
Run failing tests to verify correctness
Let me read the current state of the relevant files:
→ Read lib/liquid-fixpoint/src/constraint_with_env.rs 
→ Read lib/liquid-fixpoint/src/constraint_solving.rs 
→ Read lib/liquid-fixpoint/src/lib.rs 
Thinking: Now let me look at the graph.rs file to understand topological_sort_sccs:
Now let me check the graph.rs to understand topological_sort_sccs:
→ Read lib/liquid-fixpoint/src/graph.rs 
Thinking: Now I have a clear picture. Let me implement the SCC+rank algorithm in compute_non_cuts. Based on the pseudocode in the summary and my understanding of the code:
1. compute_non_cuts should:
   - Compute ranks via self.constraint.kvar_ranks(n_max)
   - Compute dep_graph via self.constraint.kvar_dep_graph()
   - Get SCCs via graph::topological_sort_sccs(&dep_graph)
   - For each SCC, apply scc_dep logic
2. scc_dep (free function outside impl block):
   - Singleton without self-loop → non-cut
   - Multi-node SCC: pick min-rank kvar as cut, remove it, recompute SCCs on subgraph, recurse
I need to be careful about identifying which SCCs are cyclic, checking for self-loops in singletons, and building the sub-graph correctly when recursing on multi-node SCCs.
The topological_sort_sccs function returns SCCs in topological order, and since edges in the dep_graph represent dependencies (k0 → k1 means k0 depends on k1), a kvar with no outgoing edges is acyclic and can be eliminated. I should start the leaf-peeling approach with kvars that have no dependencies.
For the SCC approach, singleton SCCs without self-loops are non-cuts, but multi-node cycles require selecting a cut kvar. The recursion works by picking the minimum-rank kvar from a cycle, removing it as a cut, then recursively processing the remaining kvars until all cycles are resolved. Writing the recursive function... Building the subgraph... Checking the type signatures for the HashSet operations - scc.iter() yields &T::KVar items, so remaining becomes HashSet<&T::KVar>, and calling contains(dep) where dep: &T::KVar should work as long as T::KVar implements Eq and Hash.
But there's a lifetime problem here - remaining borrows from scc, so those references are tied to scc's lifetime. To sidestep this, I'm cloning the values to create an owned HashSet<T::KVar> instead. Then I'm building a subgraph by iterating through the remaining nodes and filtering their dependencies to only include those still in the remaining set...
Building the subgraph HashMap... Finishing up the function by computing strongly connected components from the dependency graph, then iterating through each SCC to identify non-cuts, and finally converting the results to formatted strings. I should also clean up those debug print statements scattered throughout the constraint file. Now I'm mapping out the specific edits needed: removing those debug statements from eliminate_acyclic_kvars, rewriting compute_non_cuts to implement the SCC and rank-based algorithm, and adding the helper function for computing strongly connected components. I also need to make sure HashSet is imported in the imports section and clean up the debug output in lib.rs. I need to make sure the recursive call passes the sub-graph rather than the original dependency graph, and I'm verifying that the self-loop check correctly identifies when a singleton node has a self-reference within that sub-graph.
Now I'm ready to implement the changes: I'll update the imports to include HashSet, strip out the debug statements, rewrite the compute_non_cuts function with the new algorithm, add the scc_dep helper function, and clean up any remaining debug output.
