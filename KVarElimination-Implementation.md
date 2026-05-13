KVar Elimination  Implementation Map
====================================

Purpose
-------
This document maps the implementation of KVar (predicate-variable) elimination
and syntactic solving in this repository. It is intended to be consumed by an
automated agent that will compare another implementation against this repo (the
source-of-truth). The file points to the exact modules/functions and explains
how the pieces fit together so the comparator can focus on functional
equivalence rather than reading the entire codebase.

This file is AI-generated; use it as a structured guide and verify details by
inspecting the referenced source files.

High-Level Overview
-------------------
There are two related concerns implemented here:

1. Identification: decide which KVars can be eliminated (the "cut" vs
   "non-cut" decision). This is graph-based: build a constraintKVar graph,
   compute SCCs, and pick KVars (cuts) whose removal makes the graph acyclic.

2. Syntactic solving / materialization: for KVars that are not cut (or when
   the Horn pipeline chooses to syntactically eliminate), construct a
   syntactic representation (binder environments + substitutions, called
   "cubes") and convert those cubes into concrete predicates (existentials +
   equalities + inner predicates). These predicates are then used by the
   refinement/verification pipeline.

Primary Source Locations (what to read)
--------------------------------------
Read these files and the listed functions. Each entry includes a short
description of its role.

1) Dependency graph and cut selection

- `src/Language/Fixpoint/Graph/Deps.hs`
  - `kvEdges`  build constraintKVar bipartite edges used by the graph.
  - `elimVars`  main entry that returns graph edges and `Elims` (cuts and
    non-cuts).
  - `edgeDeps`, `edgeDeps'`, `gElims`, `sccElims`, `sccDep`, `cycleDep`  the
    SCC and cycle-based logic used to pick cuts.
  - `graphElim`  graph rewriting used when reasoning about eliminated
    KVars; used by `elimDeps`.
  - `edgeRank`, `boundElims`  rank-based and distance-bounding heuristics
    (driven by `Config.elimBound`).

2) Solver initialization (integration point)

- `src/Language/Fixpoint/Solver/Eliminate.hs`
  - `solverInfo`  constructs `SolverInfo` for the main solver. It calls
    `elimVars` to get cuts/non-cuts, computes common binder environments, and
    initializes `Sol.sHyp` (the Hyp/cube table) for non-cut KVars.
  - `kutVars` (helper)  yields `([CEdge], cutKs, nonCutKs)` used by
    `solverInfo`.
  - `nonCutHyps`, `nonCutHyp`, `nonCutCube`  compute the `Cube`s (binder
    env + substitution + metadata) that define each non-cut KVar.

3) Representation of non-cut solutions

- `src/Language/Fixpoint/Types/Solutions.hs`
  - `data Sol a`  key fields: `sMap` (concrete QBind solutions), `sHyp`
    (non-cut KVar `Hyp`), `sScp` (scopes for KVars).
  - `type Hyp = ListNE Cube` and `data Cube = Cube { cuBinds, cuSubst, cuId, cuTag }`.
  - `result` / `lookupQBind` / `lookup`  helpers to read solutions.

4) Converting cubes into predicates (syntactic solver)

- `src/Language/Fixpoint/Solver/Solution.hs`
  - `nonCutsResult` and `mkNonCutsExpr`  expose non-cut KVar results to the
    rest of the solver as delayed expressions.
  - `bareCubePred`  build a single expression for a `Cube` (used for
    presentation / saving); useful to understand the shape of the solution
    produced from a cube.
  - `apply` -> `applyKVars` -> `applyKVar`  central path that applies the
    current `Sol` to an environment. `applyKVar` calls `Sol.lookup`:
     - `Left cs` (a `Hyp`) => `hypPred` is used (cube-based expansion)
     - `Right eqs` (a `QBind`) => qualifiers are expanded via `qbPreds`.
  - `hypPred` -> `cubePred` -> `cubePredExc`  turn a cube into `(Pred, KInfo)`
    pairs; `cubePredExc` constructs existential quantifiers over the cube's
    local binders, equalities for substituted parameters, and the predicate
    body obtained by recursively calling `apply` on the cubes binder
    environment.
  - `dropUnsortedExprs` / `rapierSubstExpr`  helpers for substitution and
    filtering unsorted expressions.

5) Horn-level, source-level syntactic elimination

- `src/Language/Fixpoint/Horn/Transformations.hs`
  - `sol1`  given a KVar symbol and its scope (LCA), scan the Horn AST and
    produce a list of cubes (list of binder lists + equalities) that define
    that KVar.
  - `scope`  find LCA where KVar appears (used by `sol1`).
  - `doelim`  given a KVar and the `sol` returned by `sol1`, traverse the
    Horn constraint AST and replace occurrences of the KVar using the
    syntactic solution (rewrites heads to `true` / quantifiers / equalities
    as appropriate).
  - `elimKs'`  iterate `sol1` + `doelim` across multiple KVars.
  - Other helpers: `findKVarInGuard`, `defs`, `doelim`'s `demorgan` logic,
    and the `pokec`/`split` pipeline used to prepare constraints for elim.

6) Entry points / pipelines

- `src/Language/Fixpoint/Solver/Solve.hs`
  - `solve` / `solve_`  the main solver. If `useElim cfg` then
    `E.solverInfo` is used to initialize the solver with `sHyp` values for
    non-cut KVars.
  - `result` / `solResult` / `nonCutsResult`  integration points where the
    solved expressions are gathered for output.

- `src/Language/Fixpoint/Horn/Solve.hs`
  - `elim`  Horn mode entry that applies `Tx.elim` (Horn.Transformations)
    or `Tx.solveEbs` (existential binder solving) before calling the general
    solver.

Configuration and Flags
-----------------------
Check `src/Language/Fixpoint/Types/Config.hs` for all flags that control
elimination behavior. The most relevant are:

- `eliminate :: Eliminate` (None | Some | All | Horn | Existentials)
- `elimBound :: Maybe Int`  maximum chain length to eliminate
- `elimStats :: Bool`  print statistics about elimination
- `autoKuts :: Bool`  ignore user-specified kut (kvar cut) set
- `nonLinCuts :: Bool`  treat non-linear KVars as cuts
- `explicitKvars :: Bool`  affects Horn vs fixpoint style handling

Call Flow (compact)
--------------------
1. Parse/prepare query (Horn or FInfo). If Horn and `--eliminate=horn`, call
   `Tx.elim` (Horn.Transformations) to syntactically rewrite constraints.
2. `Solve.solve` calls `solverInfo`. If elimination is enabled `E.solverInfo`
   is used:
   - `E.solverInfo` calls `elimVars` (Graph/Deps) and `nonCutHyps` to produce
     `SolverInfo` and the `Sol.sHyp` table (cubes for non-cut KVars).
3. Solver main loop (`refine`) uses `S.lhsPred`/`apply`:
   - `apply` -> `applyKVars` -> `applyKVar`
   - `applyKVar` expands a KVar by calling `Sol.lookup`:
     * if `Left Hyp` -> `hypPred` -> `cubePred`/`cubePredExc` turn cubes into
       concrete predicates (existentials + equalities + body)
     * if `Right QBind` -> qualifiers expanded (`qbPreds`)
4. Results are packaged via `solResult` (minimization optional) and
   `nonCutsResult`.

Data Structures To Inspect
--------------------------
- `Sol` (src/Language/Fixpoint/Types/Solutions.hs): `sMap`, `sHyp`, `sScp`.
- `Cube` (same file): binder env, substitution, subc-id, tag.
- `Elims` (Graph/Deps.hs): `depCuts`, `depNonCuts` set semantics.

Concrete places where "KVar is expanded" occurs
-----------------------------------------------
- `applyKVar` in `Solver/Solution.hs`  decides whether to use `hypPred`
  (cube-based expansion) or qualifiers. This is the runtime expansion site
  used by the solver's refinement loop.
- `cubePred`/`cubePredExc`  the implementation that takes a `Cube` and
  returns an existentially quantified `Pred` plus `KInfo` (size/depth tags).

Tests / Examples
-----------------
Look at tests that exercise elimination modes (files often include a pragma
like `// fixpoint "--eliminate=some"` or smt files with `(fixpoint "--eliminate=horn")`):

- `tests/horn/pos/` and `tests/horn/neg/`  Horn elimination examples
- `tests/elim/` and `tests/pos`  assorted elimination cases referenced in
  repository tests

Suggested grep patterns (quick checks)
-------------------------------------
Run these in the repository root to find the relevant code paths quickly:

```
rg "\\belimVars\\b|\\bkvEdges\\b|\\bgraphElim\\b"
rg "\\bsolverInfo\\b.*Eliminate|\\bkutVars\\b|\\bnonCutHyps\\b"
rg "\\bsol1\\b|\\bdoelim\\b|\\belimKs'\\b|\\bfindKVarInGuard\\b"
rg "\\bapplyKVar\\b|\\bhypPred\\b|\\bcubePred\\b|\\bcubePredExc\\b|\\bbareCubePred\\b"
rg "\\bsMap\\b|\\bsHyp\\b|\\bCube\\b|\\bcuSubst\\b|\\bcuBinds\\b" src
rg "--eliminate|elim-stats|elimBound" -S
```

Comparator Checklist (what to compare)
-------------------------------------
1. Graph construction: does the other implementation build the same
   constraintKVar bipartite graph? Equivalent of `kvEdges` and `kvReadBy`?
2. SCC / cut selection: does it compute SCCs and pick cuts similarly? Map
   heuristics (`sccElims` / `edgeDeps`) and flags (`elimBound`, `nonLinCuts`).
3. Solution representation: are non-cut solutions stored as cubes (binder
   environment + substitution + metadata)? (Compare to `Cube`.)
4. Cube  predicate: does the other implementation produce existentials +
   equalities + body (as `cubePredExc` does)? Are free parameters preserved
   as equalities, and local binders quantified?
5. Integration point: does the solver expand KVars on-the-fly during `apply`?
   Or does it pre-rewrite constraints like Horn.Transformations' `doelim`?
6. De-duplication / simplification: compare behavior of `simplifyKVar` and
   any minimization steps (e.g. `minimizeResult`).
7. Edge cases: check handling of unsorted expressions in substitutions
   (`dropUnsortedExprs`), alpha-equivalence checks and existential elimination
   simplification (`simplifyKVar`).

Useful background reference
---------------------------
The solver comments reference: "Local Refinement Typing", ICFP 2017
(R. Jhala et al.)  the fusion / cut elimination idea is described there and
matches the high-level approach used in `Solver.Eliminate`.

Notes and caveats
-----------------
- This document is a concise roadmap. The authoritative reference is the
  source code itself (files listed above).
- The code base contains both a Horn-level syntactic elimination pass
  (`Horn/Transformations.hs`) and a runtime expansion mechanism used by the
  general solver (`Solver/Solution.hs`). The comparator should check which
  approach the other implementation uses (pre-rewrite vs. on-the-fly
  expansion) and compare behavior for both.

AI disclosure
------------
This mapping was created by an automated assistant (AI). It is derived from
static inspection of the repository and intended to guide another automated
agent's comparison. Validate any behavioral assumptions by running the test
suite or inspecting the referenced functions.
