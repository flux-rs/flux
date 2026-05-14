Goal
Compare the rust-side implementation of KVar acyclic elimination (rust-fixpoint) against the external fixpoint binary, identify discrepancies, and fix them. Specifically, we want the set of "non-cut" (acyclic) KVars identified by our in-crate Rust solver to match what the external Haskell fixpoint binary reports in its nonCutsSolution JSON field.
Instructions
- Do not use xtask to build/run things — it hangs. Instead, build with cargo build --bin flux-driver --features rust-fixpoint and run tests using:
    FLUX_SYSROOT=/home/cole/research/flux/sysroot \
  FLUX_DRIVER=/home/cole/research/flux/target/debug/flux-driver \
  /home/cole/research/flux/target/debug/flux \
    --edition=2021 --crate-type=rlib <path-to-test.rs>
  - The xtask test surface --rust-fixpoint command can be used for bulk test output (with timeout 10s in front) — it does successfully build and emit mismatch JSON to stderr before hanging/completing.
- Key references: docs/agents/compare_kvars.md and KVarElimination-Implementation.md.
Discoveries
Agent's prior commit (72659be3d8) — sanity check results
The previous agent added:
1. Task::run_external() in lib/liquid-fixpoint/src/lib.rs — always invokes the external fixpoint binary (duplicates the #[cfg(not(feature="rust-fixpoint"))] arm of Task::run()). Correct.
2. Task::rust_non_cuts() — builds a ConstraintWithEnv and calls compute_non_cuts(). Correct.
3. ConstraintWithEnv::compute_non_cuts() — calls eliminate_acyclic_kvars() and returns kvar names as strings. Correct (also had an unused use z3::Solver import — minor warning, now fixed).
4. eliminate_acyclic_kvars() was changed to return Vec<T::KVar> instead of (). Correct.
5. Comparison in fixpoint_encoding.rs::run_task_with_cache() — always calls run_external(), and under #[cfg(feature="rust-fixpoint")] compares the sets, emits JSON to stderr, panics on mismatch. Correct.
The mismatch pattern
Running xtask test surface --rust-fixpoint (or individual tests like tests/tests/pos/structs/dot01.rs) shows mismatches like:
{"def":"mk_pairs_with_bound###Body","external":["k4","k5"],"extra_in_rust":[],"missing_in_rust":["k4","k5"],"rust":[]}
The rust side always finds zero non-cuts (rust: []) while the external fixpoint finds several.
Root cause investigation — kvar_dep_graph
The function Constraint::kvar_dep_graph() in lib/liquid-fixpoint/src/constraint_solving.rs builds a KVar→KVar adjacency map. In its ForAll arm it was:
Constraint::ForAll(bind, cstr) => {
    deps.extend(bind.pred.kvars());
    go(cstr, deps, graph);
}
Problem: It only adds graph entries for kvars in head position (Constraint::Pred). Kvars that appear only in assumption position (in ForAll binder predicates) are pushed into deps but never added as keys to the graph. This caused eliminate_acyclic_kvars to find zero "empty-dep" nodes and immediately return [].
Fix applied (in constraint_solving.rs): Before extending deps, register each assumption kvar in the graph with the current outer deps:
Constraint::ForAll(bind, cstr) => {
    for kvar in bind.pred.kvars() {
        graph.entry(kvar.clone()).or_default().extend(deps.iter().cloned());
    }
    deps.extend(bind.pred.kvars());
    go(cstr, deps, graph);
}
NEW problem discovered after the fix
After applying the fix and adding debug output, the dep_graph for dot01.rs shows:
k0:[k0,k1], k1:[k0,k1],
k2:[k0,k1,k4,k5], k3:[k0,k1,k4,k5],
k4:[k0,k1,k2,k3], k5:[k0,k1,k2,k3]
- k0 has a self-loop (depends on itself) — it's a cut.
- k1 also has a self-loop — it's a cut.
- k2 depends on k4, and k4 depends on k2 → apparent cycle between k2↔k4, k2↔k5, k3↔k4, k3↔k5.
But the external fixpoint says k4 and k5 ARE non-cuts. This means our dep_graph is computing spurious cyclic dependencies between k4/k5 and k2/k3 that don't reflect the actual constraint structure.
The iterative leaf-peeling in eliminate_acyclic_kvars is fundamentally different from the SCC-based algorithm the Haskell fixpoint uses. But more immediately, the dep_graph itself appears to be computing incorrect dependencies — k4 and k5 shouldn't be in cycles with k2/k3 according to the external fixpoint.
The next step is to understand why the dep_graph produces spurious cycles for k4/k5 by inspecting the actual constraint structure sent to fixpoint. We were in the middle of trying to dump the constraint when the conversation was cut off.
Accomplished
- ✅ Reviewed and sanity-checked the previous agent's commit — no fundamental structural errors
- ✅ Found failing test cases: tests/tests/pos/structs/dot01.rs, tests/tests/pos/structs/dot02.rs, tests/tests/pos/surface/bsearch.rs, tests/tests/pos/surface/bsearch1.rs all fail with rust: []
- ✅ Fixed the first bug: assumption-only kvars not being added to the dep_graph (edit to constraint_solving.rs)
- ✅ Fixed unused import warning in constraint_with_env.rs
- ✅ Added debug output to eliminate_acyclic_kvars to print the dep_graph
- 🔄 In progress: Diagnosing why the dep_graph still shows false cycles after the fix. The dep_graph shows k4↔k2, k4↔k3, k5↔k2, k5↔k3 cycles that shouldn't exist per the external fixpoint. Need to dump the raw constraint to understand the actual structure.
- ❌ Not yet done: Root cause of the spurious cycles is unknown; the actual fix for the dep_graph algorithm may require a different approach (e.g., SCC-based rather than leaf-peeling, or a fix to how deps accumulate across Conj branches).
Relevant files / directories
Modified files
- lib/liquid-fixpoint/src/constraint_solving.rs — kvar_dep_graph() ForAll arm: added assumption kvar registration (the fix, lines ~80-95); this is the main file to continue working on
- lib/liquid-fixpoint/src/constraint_with_env.rs — eliminate_acyclic_kvars() now returns Vec<T::KVar>; has temporary debug eprintln! for dep_graph; compute_non_cuts() had unused import removed
- crates/flux-infer/src/fixpoint_encoding.rs — run_task_with_cache() modified to always call run_external() and do comparison under #[cfg(feature="rust-fixpoint")]
- lib/liquid-fixpoint/src/lib.rs — added Task::run_external() and Task::rust_non_cuts() methods
Key reference files (read-only)
- docs/agents/compare_kvars.md — how to run the harness
- KVarElimination-Implementation.md — map of Haskell fixpoint KVar elimination (the ground truth)
- lib/liquid-fixpoint/src/constraint_solving.rs — kvar_dep_graph, elim, sol1, scope, do_elim
- lib/liquid-fixpoint/src/constraint_with_env.rs — solve_by_fusion, eliminate_acyclic_kvars, compute_non_cuts
- tests/tests/pos/structs/dot01.rs — minimal failing test case
- tests/tests/pos/surface/bsearch.rs — another failing test
Key investigation needed
The Conj branches in the constraint likely cause the dep_graph to accumulate deps incorrectly. In a Conj([ForAll(bind={k2,...}, head=k4), ForAll(bind={k4,...}, head=k2)]), branches are correctly isolated by deps.truncate(n), but with assumption kvars now being registered, the or_default().extend() call may accumulate deps from multiple branches onto the same kvar node. The dedup() at the end of kvar_dep_graph only removes adjacent duplicates, not all duplicates — though that's cosmetic. The actual spurious cycle needs to be traced by inspecting the constraint structure, which requires either dumping it (find where -Fdump-constraint writes its output) or adding Display debug output for the constraint tree.
