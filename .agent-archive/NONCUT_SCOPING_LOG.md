# Non-Cut Scoping Log

## What We Changed
- Added temporary diagnostics around non-cut elimination and free-var reporting.
- Disabled pre-fixpoint non-cut elimination for now so we can inspect raw fixpoint output.
- Added encoder-side filtering for obvious non-issues in the diagnostic path:
  - `Var::Const(..)`
  - `Var::DataProj { .. }`
  - `Var::TupleProj { .. }`

## What We Observed
- `const00` was a false positive from the diagnostic checker.
- `tuple_encoding` was only flagging projection vars and now passes once those are ignored.
- `too_many_linked_lists` was the interesting case.
- Our own non-cut rendering shows existential binders like `∃ Local(1):Int, Local(2):Int`.
- Raw fixpoint output shows those same non-cut solutions as lambdas with explicit bound args like `$k1##1`, `$k1##2`.

## Current Suspicion
- `sol1` may not be the real problem.
- The more likely issue is the substitution / elimination path around non-cut KVars.
- We should compare three things side by side:
  1. old elim logic on `main`
  2. Haskell liquid-fixpoint behavior
  3. current Rust code

## Next Checks
- Compare the old `elim_non_cut_kvars` implementation on `main` with the current code.
- Trace whether `Local(1)` is introduced by the scoping reconstruction or lost during substitution.
- Inspect whether our `fmt_cube_pred` / `kvar_scope` logic is closing over the right variables.
- Keep the diagnostic loop running on one failing case at a time until we know which var classes are real and which are noise.

## Notes
- Do not re-enable pre-fixpoint non-cut substitution until the scoping story is understood.
- The untracked files already in the worktree were intentionally left alone.
