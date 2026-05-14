Title: Compare rust-fixpoint Non-Cut KVars Against External Fixpoint

Purpose
-------
Automated agents should use the repository's test harness to discover and
explain discrepancies between the in-crate rust-fixpoint solver and the
external `fixpoint` binary with respect to the FIRST-phase non-cut (acyclic)
KVar elimination. The agent's job is to run the harness, reproduce mismatches,
and gather artifacts that make diagnosis straightforward (task/constraint,
external JSON, rust-side eliminated kvars, and a stable task id).

Background / references
-----------------------
- The in-repo Rust implementation lives under `lib/liquid-fixpoint/`.
- A high-level map of KVar elimination is in `KVarElimination-Implementation.md`.
- The rust-side acyclic elimination is implemented in
  `lib/liquid-fixpoint/src/constraint_with_env.rs` (see
  `eliminate_acyclic_kvars`). The external-run harness lives in
  `crates/flux-infer/src/fixpoint_encoding.rs` (see `run_task_with_cache`).

Goal
----
1. Run the project's tests (or a targeted subset) with the `rust-fixpoint`
   feature enabled so both the external fixpoint and the in-crate solver run.
2. Detect the first test where the external `fixpoint`'s non-cut set differs
   from the rust-side acyclic-elimination set.
3. Gather and emit the following artifacts for that failing task:
   - The task key / stable id (from FixpointQueryKind::task_key)
   - The textual constraint / task that was sent to the external fixpoint
     (dumped by the harness when `-Fdump-constraint` is enabled).
   - External `fixpoint` JSON (stdout) for the query (the harness already
     parses this into VerificationResult). Save raw JSON for inspection.
   - The list of KVar names the rust-side eliminated (e.g. `["k0","k1"]`).

How to run the harness
----------------------
From the repository root:

1. Build the sysroot and the `flux` binary with the rust-fixpoint feature.

   Use the included xtask helper (recommended):

   - Build and run a single test:

     cargo run -p xtask -- run tests/tests/pos/surface/alias00.rs --rust-fixpoint

   - Or run the entire `pos/surface` directory (this will take longer):

     cargo run -p xtask -- test -- --filter surface --rust-fixpoint

2. Alternatively, run the flux binary directly after building sysroot with
   `xtask` or `cargo`:

   export FLUX_SYSROOT=$PWD/sysroot
   target/debug/flux --crate-type=rlib --edition=2021 -Ztrack-diagnostics=y <path-to-test.rs>

Notes about flags
-----------------
- Enable the `rust-fixpoint` feature when building the `flux` driver so the
  in-crate solver is available. xtask exposes `--rust-fixpoint` to automate
  this.
- To dump the constraint text sent to `fixpoint`, pass `-Fdump-constraint` to
  the `flux` invocation (the xtask run helper can be extended to include
  this flag in `flags` when needed).

Where the comparison happens
----------------------------
- The comparison is performed inside
  `crates/flux-infer/src/fixpoint_encoding.rs::run_task_with_cache`. It:
  1. Always runs the external `fixpoint` binary (Task::run_external()).
  2. When built with `rust-fixpoint`, calls Task::rust_non_cuts() (which
     constructs a `ConstraintWithEnv` and calls `compute_non_cuts` ->
     `eliminate_acyclic_kvars`).
  3. Compares the two sets and emits a compact JSON to stderr and panics on
     mismatch. The JSON includes `def`, `external`, `rust`, `missing_in_rust`,
     and `extra_in_rust`.

Useful entry points (code references)
-------------------------------------
- lib/liquid-fixpoint/src/constraint_with_env.rs::eliminate_acyclic_kvars
- lib/liquid-fixpoint/src/constraint_with_env.rs::compute_non_cuts
- lib/liquid-fixpoint/src/lib.rs::Task::run_external
- lib/liquid-fixpoint/src/lib.rs::Task::rust_non_cuts
- crates/flux-infer/src/fixpoint_encoding.rs::run_task_with_cache
- KVarElimination-Implementation.md (high-level map and pointers)

What the agent should produce when a mismatch is found
-----------------------------------------------------
1. The JSON emitted by the harness (already printed to stderr).
2. The dumped constraint text (from -Fdump-constraint).
3. The external fixpoint JSON output for the task.
4. A short summary that maps the rust KVar names (k0,k1,...) to their
    originating kvar IDs in the fixpoint encoding, if possible (the agent can
    use `crates/flux-infer/src/fixpoint_encoding.rs` mappings to trace ranges of
    `fixpoint::KVid` back to `rty::KVid`).

Note on interpretation
----------------------
- If the external `fixpoint` finds a non-cut for a KVar but the rust-side does
  not, that generally indicates the rust implementation is missing an
  optimization and is more conservative (this is usually acceptable but worth
  investigating).
- If the rust-side finds strictly more non-cuts than the external `fixpoint`,
  that's usually good (rust found a stronger acyclic elimination), but it is
  also suspicious because the external tool is the long-tested ground truth.
  Treat this case as a potential bug: gather artifacts (dumped constraint,
  external JSON, rust eliminated list) and investigate the dependency graph
  construction and KVar encoding mapping for mistakes.

Practical tips
--------------
- The agent can reproduce the failing case by re-running only the failing
  test file with the `flux` binary, enabling `-Fdump-constraint` to capture
  the exact input to the external `fixpoint` binary.
- The code in `lib/liquid-fixpoint` is the authoritative reference for how the
  rust-side elimination works; KVarElimination-Implementation.md is a compact
  guide and will help focus the investigation.
- If the agent needs the repository checked out in a different location, ask
  the user where to clone it or request a path to an existing local checkout.

If anything is unclear or you need the harness to emit additional artifacts
(e.g., more verbose logs, a mapping from fixpoint::KVid to source kvar ids,
or writing outputs to files instead of stderr), say which outputs you want and
I will make the changes.
