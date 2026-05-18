# Eliminate non-cut kvars before handing constraints to fixpoint

## Summary

Mirrors liquid-fixpoint's [FUSION-style][fusion-comment] non-cut
kvar elimination on the Flux side: classify each `Pred::KVar`
emitted into the constraint as either *cut* or *non-cut*,
syntactically inline every non-cut kvar's defining cubes at each
of its use sites, and ship the resulting (cut-only) constraint to
fixpoint.

The reference implementation lives in `Solver/Solution.hs`
(`cubePred`, `hypPred`, `elim1`, ... in liquid-fixpoint
`develop`). This PR ports the same algorithm to Rust, exposes it
via two public methods on `Constraint`/`ConstraintWithEnv`:

```rust
fn compute_non_cuts(&self) -> HashSet<KVid>;
fn elim_non_cut_kvars<F>(&mut self, fresh: &mut F)
where F: FnMut() -> T::Var;
```

and wires `elim_non_cut_kvars` into the encoder right before the
constraint is rendered to the `.smt2` byte stream.

[fusion-comment]: https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/src/Language/Fixpoint/Solver/Solution.hs

## Motivation

When Flux drives liquid-fixpoint, every Flux-level Horn constraint
becomes a `(constraint ...)` in the emitted `.smt2`. The set of
`$kN` references in that constraint splits naturally into:

- **Cut kvars** — those that participate in a recursive cycle in
  the kvar dependency graph. Fixpoint must solve these
  iteratively, narrowing each kvar's default solution against
  qualifiers until a fixed point is reached.
- **Non-cut kvars** — those that do *not* participate in a
  recursive cycle. Their solution is uniquely determined by the
  conjunction of their defining cubes; there is no fixed-point
  computation involved. We can substitute them out syntactically
  before fixpoint even sees the constraint.

Pre-eliminating non-cut kvars on the Flux side gives us:

1. **Smaller constraints handed to fixpoint** (cut kvars only), so
   the solver iterates over a strictly smaller graph.
2. **Solutions for non-cut kvars produced by Flux directly**,
   rather than recovered from fixpoint output. This eliminates a
   class of round-trip mismatches we'd hit when the Haskell and
   Rust solvers disagreed on how to normalize an eliminated
   kvar's body.
3. **Closer parity with liquid-fixpoint's own pipeline**, which
   makes the Rust port (`rust-fixpoint` feature) much easier to
   keep aligned with the reference Haskell solver.

## What changed

### Public API

- `Constraint::compute_non_cuts(&self) -> HashSet<T::KVid>` —
  build the kvar dependency graph and return the set of non-cut
  kvars (kvars that do not participate in any cycle).
- `Constraint::elim_non_cut_kvars<F>(&mut self, fresh: &mut F)` —
  for each non-cut kvar, collect its cubes from the constraint,
  rewrite every use site to inline those cubes (replacing
  `Pred::KVar(k, args)` with the appropriate `Pred::Hyp(cubes)`),
  and drop the original defining constraints. `fresh` supplies
  fresh `T::Var`s for per-cube binder freshening at use sites.
- Convenience shims on `ConstraintWithEnv` that forward to the
  underlying `Constraint`.

### New constraint shape

`Pred` grows a new variant:

```rust
Pred::Hyp(Vec<Cube<T>>)

struct Cube<T: Types> {
    extra_binders: Vec<Bind<T>>,
    body: Box<Pred<T>>,
}
```

A `Pred::Hyp(cubes)` renders on the wire as

```
((or (exists ((b1 t1) ...) <body1>)
     (exists ((b2 t2) ...) <body2>)
     ...))
```

i.e. the disjunction of the existentially-bound cube bodies. Single-
and zero-cube cases collapse to the appropriate degenerate shape
(`(<body>)` and `(false)` respectively). Cube bodies may themselves
contain `Pred::KVar`s (for cut kvars), `Pred::And`s, nested
`Pred::Hyp`s, etc. The full emitted grammar is documented in
`lib/liquid-fixpoint/src/format.rs::fmt_hyp_expr_paren` /
`fmt_pred_as_expr`.

### Elimination algorithm

Ports `cubePred`/`hypPred`/`elim1` from
`Solver/Solution.hs::elim1_v2`. For each non-cut kvar `$k`:

1. Walk the constraint to collect every defining cube of `$k`
   (each cube is a chain of `(forall ...)` binders culminating in
   `(... ($k arg0 arg1 ...))`). The bound variables of the
   `forall` chain become the cube's `extra_binders`; the chain's
   guards/atoms become the cube body.
2. Walk the constraint *again* to find every *use* site of `$k`
   (a `Pred::KVar(k, args)` not in defining position).
3. At each use site, substitute the args into a fresh copy of
   each cube (renaming `extra_binders` to fresh names) and
   replace the `Pred::KVar` with the resulting `Pred::Hyp`.
4. Drop the original defining `forall`s (their bodies become
   trivially-`true` after the kvar is gone).

Substitution is FUSION-style: existential binders inside a cube
are preserved (not eagerly eliminated), matching what
`bareCubePred` does in the Haskell solver. Per-cube freshening
happens at the use site, not at collection time, so two distinct
use sites of the same kvar get distinct binder names.

### Encoder integration

`create_task` (in `flux-infer/src/fixpoint_encoding.rs`) now calls
`elim_non_cut_kvars` on the assembled constraint before formatting
the `.smt2` byte stream. The freshener uses the encoder's local
variable counter (`LocalVarEnv`).

### Fixpoint flag

`Task::run` now passes `--allow-deep-kvars` to fixpoint. This
flag is added in the [companion liquid-fixpoint
PR](#companion-liquid-fixpoint-pr); it opt-in enables the parser
support and post-elaboration deep-resolve sweep that this PR
relies on.

### Identifier trait extensions

Two new methods on `Identifier`:

- `is_anonymous()` — true for identifiers that don't carry a
  user-visible name (e.g. the `_` binder for a unit guard). Lets
  the elimination pass skip pointless renaming.
- `is_local()` — true for identifiers that originate inside a
  particular Flux query (vs. constants/decls from the module
  scope). Lets the freshener decide which binders need renaming
  on a per-cube basis.

Default implementations preserve current behavior; Flux's `Var`
overrides both.

### Formatter / `cstr2smt2`

- `format.rs` gains the `Pred::Hyp` arm and the new
  `fmt_hyp_expr_paren` / `fmt_cube_expr` / `fmt_pred_as_expr`
  helpers. The Lean format printer (`lean_format.rs`) gains the
  matching arm.
- `cstr2smt2.rs` panics on `Pred::Hyp` (it's not part of the
  Flux internal SMT pipeline; only the fixpoint pipeline ever
  sees this variant).

## Companion liquid-fixpoint PR

Requires the following commits on liquid-fixpoint branch
`fix/elabFSetBagZ3-pexist-binders` (currently unmerged):

- `4c6d8356` — `SortCheck.elabFSetBagZ3` rewrites Set/Bag sort
  annotations on `PExist`/`PAll`/`ELam`/`ECst` binders, so that
  Flux's elaborated cube bodies with `Set_*`-typed binders
  type-check.
- `53bf6f4c` — `Horn.Parse` accepts the `Pred::Hyp` on-the-wire
  grammar under `--allow-deep-kvars`.
- `5f18448b` — `Solver.Solution.apply`/`applyInSortedReft` sweep
  `PKVar` nodes left buried inside concrete preds and resolve
  them via `applyKVar`, under `--allow-deep-kvars`.

Without those commits, fixpoint rejects Flux's emitted constraints
at parse time. See `PR_DESCRIPTION_elabFSetBagZ3.md` and
`PR_DESCRIPTION_allowDeepKVars.md` on that branch for details.

## Testing

- All Flux test suites pass (504 pos / 0 fail; 431 neg / 0 fail)
  with the patched fixpoint binary on `PATH` and
  `--allow-deep-kvars` enabled. Without non-cut elimination, the
  same suites pass; without the fixpoint flag, 32 tests fail at
  the fixpoint parser with `unexpected "$kN ..."`.
- The `rust-fixpoint` feature has one pre-existing build error in
  `constraint_with_env.rs:166` that is **not** caused by this PR
  (it pre-dates the branch).

## Out of scope

- Audit / improvement of cut-kvar classification heuristics. We
  use the same coarse "strongly-connected components" notion as
  the Haskell solver; refining the cut set is a separate concern.
- The `rust-fixpoint` solver's own treatment of these shapes (its
  pre-existing build break is left alone).
- Performance measurements. The motivating goal is correctness
  parity, not throughput.
