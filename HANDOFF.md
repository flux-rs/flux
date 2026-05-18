# Handoff: wick-eval-on-noncut merge — kmeans bench

## Where we are

Merge commit `c16dea9f21` on branch `wick-eval-on-noncut`. Build is clean
with `--wick` (no `--rust-fixpoint`). pldi23/kmeans bench now runs through:
- weak-kvar QE / solution loop (`Looking for weak kvars that might solve…`)
- emits human-readable function refinement solutions (e.g. `normalize_centers`,
  `add`)
- invokes external fixpoint binary
- tripping at parse-time assertion when fixpoint returns a non-cut solution
  that flux's local `compute_non_cuts` did NOT identify as non-cut.

## Build / run

```
cd /home/cole/research/flux && cargo xtask --wick install
rm -rf /home/cole/research/flux-wick-benchmarks/target/flux
cd /home/cole/research/flux-wick-benchmarks/benchmarks/pldi23
FLUXFLAGS="-Fuser-interactions-file=/home/cole/research/flux-wick-benchmarks/userinputs/kmeans.inputs \
           -Fcache=/home/cole/research/flux-wick-benchmarks/target/cache" cargo flux
```

(Build with **`--wick` only**, NOT `--rust-fixpoint`. The QE wkvars path uses
z3 directly via `cstr2smt2.rs`; the actual fixpoint solve goes through the
external `fixpoint` binary at `~/.local/bin/fixpoint`.)

## What was just done in this session

1. **Discovered missing `elim_non_cut_kvars` call** in merged
   `fixpoint_encoding.rs::check`. Re-added it (mirrors cleanup-noncut commit
   `37cfc0d9eb`), gated on `#[cfg(not(feature = "rust-fixpoint"))]`. Placed
   it BEFORE the wick QE block so wkvars analysis sees the post-elim
   constraint (with Hyps), as the user instructed.

2. **Added Hyp support to `cstr2smt2.rs::pred_to_z3`**. New helper
   `cube_to_z3` translates a `Cube` to z3 as
   `exists extra_binders. (and binder_preds... body)`, and `Pred::Hyp(cubes)`
   becomes `(or cube_to_z3(c) for c in cubes)`. Mirrors the textual rendering
   in `format.rs::fmt_hyp_expr_paren`. Empty Hyp → `false`. No binders →
   skip the exists wrapper.

3. **Other Hyp arms exist throughout constraint.rs / constraint_solving.rs,
   but many of them look wrong or at least suspicious.** They were added in
   cleanup-noncut as placeholder/conservative impls and were never stressed
   by the wick code path before this merge. Earlier in this session I
   claimed several of these were "already handled" — that was overly
   optimistic. They compile and silence the warnings, but their semantics
   for the wick QE / flattening pipeline are not obviously correct.

   Specific spots to scrutinize and ask the user about:

   - `constraint.rs::Pred::free_vars` (line 622) returns `HashSet::new()`
     for `Pred::Hyp(_)`. That is almost certainly wrong: cube bodies refer
     to outer-scope vars; `extra_binders` shadow only their own names.
     Anything that uses `free_vars` to decide scope (e.g. closing
     existentials, choosing which constants to declare, deciding what is
     in scope at a use site) will silently be wrong.

   - `constraint.rs::Pred::wkvars_in_conj` (line 646) returns `vec![]` for
     `Hyp`. Probably fine *for now* — cubes shouldn't contain wkvars in
     practice because wkvars come from elaboration and non-cut elim runs
     over the encoded fixpoint constraint — but worth confirming.

   - `constraint.rs::Pred::strip_wkvars` (line 656) returns `self.clone()`
     for `Hyp`. Same caveat: if a cube body ever contains a wkvar (e.g.
     because of ordering changes between elim and wick), this silently
     leaves it in.

   - `constraint.rs::FlatConstraint::add_assumption` (line 191) treats a
     `Pred::Hyp` as an opaque single assumption (inserted whole, no
     decomposition). For wkvars analysis (`wkvars_in_conj`,
     `has_wkvar_reachable_by_split`, the `wkvars_and_constrs` frontier in
     constraint.rs:230) this means the contents of the Hyp are invisible.
     If a cube's `body` references things that should split or hoist for
     the wkvar pipeline, we won't.

   - `constraint_solving.rs::contains_kvars` / `::kvars` (lines 379, 388)
     recurse into cube bodies — those look plausibly correct.

   - `constraint_solving.rs::elim1_v2` substitution arms (lines 427, 537)
     re-construct `Pred::Hyp(...)` over recursively-substituted cubes.
     Plausible but the cube `extra_binders` are not alpha-renamed; if a
     cut-kvar elim ever introduces a name collision with a cube binder,
     this will silently capture. Probably OK in practice but not
     defensively safe.

   - `cstr2smt2.rs::cube_to_z3` (added this session): the cube binders are
     pushed into `env` with `env.insert` then popped with `env.pop`. That
     uses the *outer* var namespace rather than a fresh layer
     (`push_bvar_layer` / `pop_layer`), which is how `Expr::Exists` does
     it. If two sibling cubes use the same binder name, or a cube binder
     name collides with an outer binder, this will misbehave. Worth
     checking whether cube binders are guaranteed fresh from
     `elim_non_cut_kvars`; if not, alpha-rename or switch to the bvar
     layering scheme.

   - `format.rs` rendering does `(or (exists (...) body) ...)` which is
     the right surface syntax; the open questions are about scope, not
     printing.

   **Action**: ask the user (or work through these one-by-one) about the
   intended semantics for each. The compile-clean Hyp arms are just enough
   to not break the build; they are not a guarantee that the wkvars/flatten
   pipeline does the right thing when Hyps are present.

4. **Added debug eprintln in two places** (not yet removed):
   - `lib/liquid-fixpoint/src/constraint_solving.rs:209` — prints
     `[flux noncut elim] non_cuts (N): k1, k2, ...` listing what flux's
     `compute_non_cuts` found.
   - `crates/flux-infer/src/fixpoint_encoding.rs:680` — prints
     `[flux pre-elim] def_id=...` and
     `[fixpoint noncut returned] def_id=... (N entries): kvar=K val=...`
     when fixpoint returns a non-empty non-cuts solution.

## The remaining bug — flux vs fixpoint non-cut disagreement

For `pldi23::kmeans::init_centers`:

```
[flux pre-elim] def_id=DefId(0:7 ~ pldi23[5549]::kmeans::init_centers)
[flux noncut elim] non_cuts (1): k3
[fixpoint noncut returned] def_id=DefId(0:7 ~ pldi23[5549]::kmeans::init_centers) (1 entries):
  kvar=k2 val=<big lambda body referencing reftgen$n$0, reftgen$k$1, a2, a3, fld0$0(...) ...>
```

So flux says k3 is the only non-cut, and eliminates it. Then fixpoint
solves the remaining constraint and *also* returns a non-cut solution for
k2 — meaning fixpoint considers k2 to also be non-cut.

**Per the user**: "we should have complete parity between fixpoint and our
implementation of non-cut kvar finding and solving (I guess do a quick
check ... has the non-cut kvar code in flux been changed by this merge?)"

### Quick check on whether non-cut code was changed in the merge

The non-cut detection / elim code lives in
`lib/liquid-fixpoint/src/constraint_solving.rs`. The merge stat for that
file:

```
lib/liquid-fixpoint/src/constraint_solving.rs |  648 +++++++++-------
```

So yes, the merge touched 648 lines in constraint_solving.rs. Worth
inspecting:

```
git log --oneline f0ed2b592e -- lib/liquid-fixpoint/src/constraint_solving.rs
```

vs

```
git log --oneline 1b33e9d900 -- lib/liquid-fixpoint/src/constraint_solving.rs
```

to confirm whether either side made changes that could explain why
`compute_non_cuts` now disagrees with what the OCaml fixpoint solver
thinks non-cut means.

### Suggested next investigation

1. Dump the encoded constraint for `init_centers` (`-Fdump-constraint` or
   inspect the smt2 file in cache) and look at which kvars appear in head
   positions vs guard positions. A kvar is "non-cut" (FUSION terminology)
   when it appears in head position somewhere and isn't part of a cycle.
   See if `k2` matches that.

2. Compare flux's `compute_non_cuts` definition to what OCaml fixpoint
   does (look in the haskell/ocaml liquid-fixpoint sources for `kuts`,
   `nonKuts`, `Cuts` etc.). The cleanup-noncut PR description in commit
   `f0ed2b592e` may explain the algorithm.

3. Check if the wick block's mutations to the constraint (the
   `flat_constraint_map`-rebuilding ForAll wrapping near line 2417
   `constraint = fixpoint::Constraint::ForAll(...)`) reintroduce or
   re-shape a kvar in a way that changes its cut-ness *after* the
   pre-elim pass already decided what to drop.

## Open questions

- **Pred::Hyp handling throughout constraint.rs / constraint_solving.rs /
  cstr2smt2.rs is probably wrong in several places.** See the detailed
  bullet list under "What was just done in this session" item 3. In
  particular `free_vars` returning empty, `add_assumption` storing Hyp
  opaquely (so wkvars analysis can't see into it), and the cube binders
  in `cube_to_z3` not using a fresh bvar layer are the most likely to
  cause silent miscompiles. Need to talk through these with the user.

- **Is `elim_non_cut_kvars` order vs wick QE correct?** Currently it runs
  before wick. After elim, Hyps replace non-cut kvar uses. wkvars analysis
  then runs over a constraint containing Hyps. Per user direction this is
  the right ordering. The new `cube_to_z3` should make the QE z3 calls
  succeed.

## Files changed in this session

```
crates/flux-infer/src/fixpoint_encoding.rs    (elim_non_cut_kvars call re-added; debug prints)
lib/liquid-fixpoint/src/cstr2smt2.rs           (Pred::Hyp → cube_to_z3)
lib/liquid-fixpoint/src/constraint_solving.rs  (debug print in elim_non_cut_kvars)
lib/liquid-fixpoint/src/constraint_with_env.rs (graph:: → crate::graph::)
```

Nothing committed in this session. `git diff --stat` to see exact state.

## Branch tips

- Merge:           `c16dea9f21` on `wick-eval-on-noncut` (current HEAD)
- cleanup-noncut:  `f0ed2b592e`
- wick-eval:       `1b33e9d900`
- Merge base:      `9cd2f8786e`
