# Handoff

## Goal
Fix non-cut KVar elimination so Flux can run without `rust-fixpoint`.

## Repo URLs
- Flux: `https://github.com/flux-rs/flux.git`
- liquid-fixpoint: `git@github.com:cole-k/liquid-fixpoint.git`
- Upstream liquid-fixpoint reference: `https://github.com/ucsd-progsys/liquid-fixpoint.git`

## Current State
- Latest commit: `13fba4370b` `Close non-cut solution scopes`
- The panic at `fixpoint_encoding.rs:740` is gone.
- The remaining problem is semantic: fixpoint still reports `Constraint with free vars` for some generated tasks.
- `cargo xtask test iter_slice00` passed earlier after the scope fix, but the full suite still has failures.

## What Was Changed
- Added `Constraint::elim_non_cut_kvars()` in `lib/liquid-fixpoint/src/constraint_solving.rs`.
- Wired Flux to call that before handing a task to fixpoint when `rust-fixpoint` is off.
- Added `scope_binders()` helper in `constraint_solving.rs`.
- Added an `Expr::Exists` display fix in `lib/liquid-fixpoint/src/format.rs`.
- Replaced the hard panic on `FixpointStatus::Crash` with a normal `QueryErr` earlier, but that change was not committed and should not be relied on.

## Suspected Issue(s)
1. The non-cut elimination path is still emitting constraints fixpoint considers ill-scoped.
2. The scoping rule likely needs to match Haskell fixpoint more precisely:
   - Haskell keeps binders in `sScp` in scope.
   - It existentially closes only vars that are free in the cube body and not in scope.
3. The current Rust side may be using the wrong place for closure.
   - `Expr::Exists` is supported in the pretty-printer, but the Rust SMT serializer still has `todo!("exists not yet implemented")` in `lib/liquid-fixpoint/src/cstr2smt2.rs`.
   - So existential closure cannot be introduced into the emitted task unless that serializer is implemented too.

## Important Evidence
- Haskell references:
  - `Language.Fixpoint.Solver.Solution.cubePred`
  - `Language.Fixpoint.Solver.Solution.bareCubePred`
  - `Language.Fixpoint.Solver.Eliminate.solverInfo`
  - `Language.Fixpoint.Types.Solutions.sScp`
- The Haskell code closes only `bs' = bs \ sScp`, not every free variable.
- Fixpoint crash payloads showed messages like:
  - `Constraint with free vars`
  - lists of vars such as `[a0]`, `[a0, a2]`, etc.

## Where To Look Next
- `lib/liquid-fixpoint/src/constraint_solving.rs`
  - `scope_binders()`
  - `do_elim()`
  - `pred_to_expr()`
- `lib/liquid-fixpoint/src/cstr2smt2.rs`
  - `Expr::Exists(..) => todo!("exists not yet implemented")`
- `crates/flux-infer/src/fixpoint_encoding.rs`
  - `KVarSolutions::closed_solutions`
  - `group_kvar_solution()`
  - `result_to_answer()`

## Suggested Next Steps
1. Decide whether closure should happen:
   - in non-cut elimination only for solver-result reconstruction, or
   - in the emitted task too, which would require implementing `Expr::Exists` serialization.
2. Compare one failing task with Haskell fixpoint output and check exactly which binders are in `sScp`.
3. Re-run:
   - `cargo xtask test iter_slice00`
   - `cargo xtask test`

## Notes
- There are unrelated untracked files left in the worktree and they were intentionally not touched:
  - `.dir-locals.el`
  - `crates/flux-infer/src/wkvars.rs`
  - `opencode.json`
