# Z3 Subprocess Backend for Suggestions

## Objective

Replace the Rust `z3` binding used by Flux's suggestion generation with the
`z3` executable selected by `PATH`. During the migration, keep both
implementations available so the existing binding backend can serve as an
oracle for correctness and performance comparisons.

This change is limited to suggestion generation. The suggestion algorithm,
liquid-fixpoint invocation, diagnostic generation, and optional
`rust-fixpoint` feature are not part of the replacement.

## Success Criteria

The subprocess backend is good enough when:

1. The existing suggestion benchmark corpus completes with the subprocess
   backend.
2. `check_validity` agrees with the binding backend on every exercised query.
3. Successful QE results are semantically equivalent, or produce equivalent
   final Flux suggestions, on the benchmark corpus.
4. Unsupported Z3 output causes a structured suggestion failure and the
   existing fallback behavior, rather than a compiler crash.
5. The `suggestions` feature no longer enables or links the `z3` crate when the
   subprocess backend is selected.
6. Runtime and process-spawn overhead are measured and reported.

Supporting every SMT-LIB construct or every possible Z3 response is explicitly
not a goal. Add parser and decoder cases only when a test or captured benchmark
query demonstrates that they are needed.

## Current Code Path

The `suggestions` feature affects three stages.

### Weak-KVar generation

- `crates/flux-middle/src/queries.rs` introduces weak KVars into inferred
  signatures.
- `crates/flux-fhir-analysis/src/lib.rs` introduces weak KVars into local
  function signatures where suggestions are permitted.

These paths do not interact with Z3 and should not change.

### Capturing suggestion inputs

`crates/flux-infer/src/fixpoint_encoding.rs`:

- Calls `make_flat_constraint_map` before function-body encoding.
- Stores flat constraints, constants, and datatype declarations in
  `SuggestionCtxt`.
- Parses ordinary cut and non-cut KVar solutions returned by liquid-fixpoint.
- Substitutes those solutions into the saved flat constraints.
- Removes unresolved ordinary KVars from assumptions.

This should remain unchanged except for passing the configured suggestion Z3
backend into the two solver operations.

### Computing suggestions

`crates/flux-infer/src/suggestions.rs`:

- Calls `FlatConstraint::wkvars_and_constrs`.
- Calls `check_validity` on sibling constraints introduced while splitting
  weak-KVar-containing disjunctions.
- Calls `qe_and_simplify` to derive a candidate predicate.
- Converts the result back to `rty::Expr` and attaches it to diagnostics.

The only public suggestion-specific Z3 operations are:

```rust
check_validity(...)
qe_and_simplify(...)
```

`qe_and_simplify` internally performs additional satisfiability queries for
vacuity pruning and one implication sanity check.

## Migration Strategy

Keep the existing binding implementation intact during the spike. Add an
independent subprocess implementation with the same logical API.

A reasonable module layout is:

```text
lib/liquid-fixpoint/src/
  cstr2smt2.rs          # existing binding implementation
  z3_process.rs         # subprocess implementation
  smt_horn.rs           # existing Horn formatter
```

Avoid a broad formatter refactor before differential testing. It is acceptable
for `z3_process.rs` initially to adapt or duplicate the relevant formatting
logic from `smt_horn.rs`. Once behavior agrees, common formatting can be
extracted safely.

## Backend Selection

Use Flux configuration, not an environment variable.

Add an enum in `flux-config`, following the existing `SmtSolver` and
`OverflowMode` patterns:

```rust
pub enum SuggestionsZ3 {
    Bindings,
    Process,
    Compare,
}
```

Expose it through a Flux flag such as:

```text
-Fsuggestions-z3=bindings
-Fsuggestions-z3=process
-Fsuggestions-z3=compare
```

During the spike, default to `bindings`. After differential testing, change the
default to `process`. The bindings and comparison modes, and all plumbing that
supports selecting between implementations, are temporary testing
infrastructure. Once the process implementation reaches parity, remove them and
remove the `z3` crate dependency from suggestion generation.

The `liquid-fixpoint` Rust library should not depend on `flux-config`. Define a
small backend enum in `liquid-fixpoint`, or pass the selected operation through
an API-level enum:

```rust
pub enum SuggestionsZ3Backend {
    Bindings,
    Process,
    Compare,
}
```

Flux maps its configuration enum to this type when calling `check_validity` and
`qe_and_simplify`. Do not read global configuration inside the library.

Do not introduce multiple compiler features for the temporary backends. During
comparison, the existing `suggestions` feature continues to enable `dep:z3`, and
the Flux flag selects which compiled implementation is called. Runtime
selection is for testing only and is not expected to avoid linking `libz3`.

After parity is established, remove the binding backend and `Compare` mode,
change `suggestions` so it no longer enables `dep:z3`, and remove any temporary
selection plumbing. The resulting process-only suggestions build must not link
`libz3`. The independent `rust-fixpoint` feature remains out of scope and may
still enable `dep:z3`.

## Process Model

Use `std::process::Command` directly:

```text
z3 -smt2 -in
```

This resolves the executable through `PATH`, matching liquid-fixpoint's normal
solver workflow.

Start with one-shot processes. A single invocation receives declarations and
one or more commands on stdin, closes stdin, and reads stdout/stderr to
completion. This avoids synchronization and response-framing complexity.

Use one invocation for:

- A validity query.
- A QE query.
- Each vacuity or sanity query, unless batching is trivial at the call site.

Process startup may be significant, but correctness and observability matter
more during the spike. Introduce a persistent process only if measurements show
that startup dominates suggestion time.

The process runner must distinguish:

- Executable not found or spawn failure.
- Failed stdin write.
- Nonzero exit status.
- Non-empty stderr associated with malformed input.
- Invalid UTF-8 if output is read as text.
- Unexpected or malformed stdout.
- `unknown`.
- QE timeout/failure.

Always include stderr and, in debug/compare output, the submitted query.

## SMT-LIB Serialization

Reuse the representations already stored in `SuggestionCtxt`. Do not introduce
a second Flux-to-SMT AST.

The formatter needs only the constructs accepted by the current binding path
and encountered by the benchmark corpus:

- `Int`, `Real`, `Bool`, `String`, fixed-width bitvectors.
- Set, map/array, and datatype applications.
- Numeral, Boolean, string, bitvector, and real constants as exercised.
- Arithmetic and comparisons.
- Boolean connectives and `ite`.
- `let`.
- Monomorphic function application.
- Theory functions currently handled by `thy_func_application_to_z3`.
- Existential expression quantifiers if they reach the suggestion query.
- Datatype declarations and constructor/accessor applications.

Use `smt_horn.rs` as the main reference for syntax. Do not call its whole-task
formatter directly because it has Horn-specific behavior and currently rejects
quantifiers and weak KVars.

### Weak and ordinary KVars

Serialize `Expr::WKVar` and weak-KVar applications as `true`, matching the
binding backend's intended behavior.

Ordinary `Pred::KVar` should have been substituted or removed before these
operations. Treat any remaining ordinary KVar as an explicit unsupported-input
error rather than silently choosing a meaning.

### Declarations

For each query, emit:

1. Datatype declarations in the existing topological order.
2. Referenced global constants.
3. Referenced binder constants.
4. Any monomorphic function-valued constants as `declare-fun`.

It is acceptable initially to emit every declaration in `SuggestionCtxt`, as
the binding backend does. Referenced-declaration filtering is an optimization or
a workaround if unrelated unsupported declarations block otherwise-valid
queries.

Peel `Sort::Func` into argument and result sorts for `declare-fun`. Do not use
the `smt_horn.rs` approximation that prints a function sort as an SMT array.

### Polymorphism

General polymorphic functions are out of scope. The suggestion context does not
contain `Task::define_funs`, and QE involving uninterpreted functions is already
best-effort.

Implement only:

- Parametric datatypes through standard SMT-LIB `declare-datatypes` with `par`.
- Concrete applications of those datatypes, for example `(List Int)`.
- `(as ctor ConcreteDatatypeSort)` when constructor result-sort disambiguation
  is required by Z3.
- Free `Sort::Var` values mapped to `Int`, consistent with Flux's existing
  `free_var_sorts_to_int` convention.
- Monomorphic UIF declarations.

If a referenced function declaration still contains `Sort::Abs` or unresolved
sort variables after this policy, return an unsupported-input error. Do not add
a general monomorphization framework for the subprocess spike.

## Validity Query

`check_validity` currently asserts all assumptions and the negated head. Emit:

```smt2
<declarations>
(assert <assumption-1>)
...
(assert (not <head>))
(check-sat)
```

Interpret responses exactly as today:

- `unsat`: valid.
- `sat`: not valid.
- `unknown`: not valid.

Change the API to return `Result<bool, SuggestionSolverError>`. There is expected
to be one caller; verify that before changing it. That caller should use
`.unwrap_or(false)`: treating a solver/process error as invalid is conservative
because it rejects the candidate branch rather than accepting an unproved
validity result.

## QE Query

Construct the same formula as the binding implementation:

```smt2
<declarations>
(assert
  (forall ((x Sort) ...)
    (=> (and <assumptions>) <head>)))
(apply (try-for (then qe nnf) 10000))
```

Preserve current behavior during migration:

- Quantify the remaining `FlatConstraint.binders`.
- Keep binder/global constants free.
- Select the last returned subgoal.
- Decode each formula in that goal.
- Choose the formula with the fewest disjuncts.
- Run the current vacuity-pruning policy.
- Run the current one-way implication sanity check.

Do not improve this policy until process/binding parity is understood.

## Deliberately Minimal Output Parsing

There are two separate parsing needs.

### Solver status

Accept exactly one of:

```text
sat
unsat
unknown
```

Whitespace may surround the token. Anything else is an error carrying stdout
and stderr. If Z3 reports that a tactic timed out or failed because of the
`try-for` limit, parse enough of the response to classify it as `QETimeout`; do
not collapse a recognized timeout into a generic malformed-response error.

### QE tactic output

The observed Z3 output is:

```smt2
(goals
  (goal
    <formula> ...
    :precision precise
    :depth 1))
```

Parse only:

- The outer `goals` list.
- One or more `goal` lists.
- Formula entries before keyword metadata.
- Metadata pairs beginning with `:`; ignore their values.

The expression decoder initially needs only the forms emitted by benchmarks.
Start with the subset already accepted by `z3_to_expr`:

- Integers and negative integers.
- `true`, `false`, and known declared symbols.
- `and`, `or`, `not`, `=>`, `=`.
- `<`, `<=`, `>`, `>=`.
- `+`, `-`, `*`, `div`, `mod`.
- `ite`.
- Known monomorphic function, constructor, and accessor applications.

Add bitvectors, strings, reals, `let`, or constructor testers when a captured
query demonstrates that Z3 returns them. Input serialization can support more
constructs than output decoding because many constructs may not survive QE.

Residual quantifiers should return `ContainsQuantifier`, preserving the current
fallback behavior.

### Parser library choice

Evaluate `smt2parser` before extending `sexp.rs`. It is a real SMT-LIB 2 parser
and handles lexical details such as quoted symbols and literals. However, it is
primarily a parser for SMT-LIB commands, while `(goals (goal ...))` is a
Z3-specific response, so it will not remove the need for a small response
wrapper or expression conversion layer.

`rsmt2` is not recommended for the first implementation. It manages solver
processes and common responses but intentionally requires callers to provide
their own expression parser, so it does not address the difficult QE-result
piece. It would also obscure the exact protocol being compared.

`lexpr` is a generic Lisp S-expression parser rather than an SMT-LIB parser. It
may be useful for the Z3-specific outer response, but its lexical compatibility
must be demonstrated before adoption.

Pragmatic decision rule:

1. Try parsing representative captured goal output with `smt2parser` in a small
   test.
2. If it cannot parse bare terms/Z3 goals cleanly, extend Flux's existing
   `sexp.rs` only for the observed output subset.
3. Do not implement speculative support for comments, exotic literals, quoted
   identifiers, or attributes unless Z3 output or a regression test requires
   it.

The experimental liquid-fixpoint `wvar-solving` branch's `Smt/Parse.hs` is a
useful reference for the output forms its real workloads encountered.

## Vacuity Pruning and Sanity Checking

Keep `prune_vacuous`'s recursive algorithm unchanged. Replace each leaf solver
operation with a textual satisfiability query containing:

- Shared declarations.
- Original assumptions.
- Relevant sibling conjuncts.
- The leaf being tested.
- `(check-sat)`.

After pruning, retain the current sanity property:

```text
candidate => original implication
```

Check it by asserting the negation and requiring `unsat`.

Initially, rebuilding a one-shot query for each pruning check is acceptable.
If timing shows this dominates, the first optimization should be batching all
checks into one process using `push`, `pop`, and response delimiters, not a
redesign of pruning.

## Differential Comparison Mode

`Compare` runs both backends for each operation.

### Validity

Compare the Boolean results directly. Record whether either backend returned
`unknown` or an internal error.

### QE

Do not compare printed expressions syntactically. Compare:

1. Success versus fallback.
2. Each result's existing sanity check.
3. Semantic equivalence when both succeed:

```smt2
(assert (not (= <binding-result> <process-result>)))
(check-sat)
```

`unsat` means the Boolean expressions are equivalent.

Use this semantic SMT query when it is straightforward to construct from the
shared declarations. If it would materially complicate the spike, compare the
decoded expressions with `==`, log mismatches together with both raw/decoded
results, and retain the logs for manual inspection. Syntactic mismatches alone
are diagnostic and do not fail the benchmark run.

Also compare final instantiated Flux suggestions, because two non-equivalent QE
normal forms may still lead to the same user-facing fallback or suggestion.

On mismatch, dump a reproducible artifact under the configured Flux log
directory containing:

- Z3 version.
- Original declarations and formula.
- Process input and raw output.
- Binding result.
- Process result.
- Semantic comparison result.
- Operation kind and source tag when available.

Comparison failures should be visible but should not prevent benchmark
completion. The wrapper should explicitly log `Ok/Err` and `Err/Ok` mismatches;
when both succeed it should compare the outputs as described above. Which result
the wrapper returns during temporary comparison is not important, provided it
is consistent and benchmark completion is preserved.

## Timing Plan

Measure backend cost inside the suggestion API rather than relying only on total
compiler wall time.

For each backend record separately:

- Number of validity calls.
- Total and maximum validity duration.
- Number of QE calls.
- Total and maximum QE duration.
- Time spent spawning/waiting for subprocesses.
- Time spent parsing/decoding.
- Number and total duration of pruning SAT calls.
- Number of successful suggestions and fallbacks.

Use `std::time::Instant`. Temporary direct printing is acceptable, as is
returning timing data for Flux to record. Prefer the existing Flux timing
infrastructure for the overall suggestion-generation run if it is easy to
extend. The temporary comparison backend should record paired
`qe_and_simplify` timings on identical inputs; these paired timings are the
primary performance comparison and do not need a predetermined pass/fail
threshold.

Benchmark procedure:

1. Use the sibling `../flux-wick-benchmarks` repository as the benchmark corpus.
2. Start with `benchmarks/flux-demo` and iterate there until the process backend
   reaches parity or a concrete, unexpectedly difficult gap is identified.
3. From the benchmark repository root, `cargo flux` runs the full corpus after
   the focused `flux-demo` work succeeds.
4. Build once before collecting timings and run each corpus once as warm-up.
5. Run each backend independently several times to avoid `Compare` mode's
   interference.
6. Run `Compare` mode once for semantic diagnostics.
7. If `flux-demo` reaches parity, report paired `qe_and_simplify` timing
   differences (and overall suggestion timing when available) before proceeding
   or stopping. If parity does not look tractable within the spike, stop and
   report the concrete blocker rather than broadening scope speculatively.
8. After `flux-demo` works, run a focused trial on the simple polymorphic vector
   workload in `benchmarks/pldi23/src/dotprod.rs`. This is a follow-up check, not
   part of the initial debugging loop; ideally the existing datatype handling
   works without further implementation.
9. Record `z3 --version`; process and binding backends may intentionally use
   different Z3 versions during the migration.

The primary expected regression is process startup. If it is material, add a
persistent process or batch pruning checks only after parity is established.

## Error Model

Replace `Z3DecodeError` with a backend-neutral suggestion solver error, while
retaining equivalent variants where useful:

```text
Spawn
Io
ProcessFailure
UnexpectedStatus
MalformedResponse
UnsupportedInput
UnsupportedOutput
ContainsQuantifier
NoResults
QETimeout
FailedSanityCheck
```

Suggestion errors remain best-effort: callers continue to use the existing
fallback to the original head expression.

## Implementation Sequence

1. Add `SuggestionsZ3` to Flux configuration and thread the mapped backend enum
   into the two `liquid-fixpoint` APIs. Keep this selection plumbing explicitly
   temporary.
2. Keep the existing `suggestions` feature enabling `dep:z3` while both
   implementations are compiled for comparison.
3. Add the one-shot `z3 -smt2 -in` runner and status parser.
4. Implement enough SMT-LIB formatting for `check_validity`; compare it against
   bindings on benchmarks.
5. Capture representative real QE outputs from the benchmark corpus.
6. Select `smt2parser` or the existing S-expression parser based on those
   captured outputs.
7. Implement only the decoder forms present in the captured corpus, starting
   with arithmetic and Boolean expressions.
8. Implement subprocess `qe_and_simplify` while preserving result selection,
   pruning, and sanity checks.
9. Add `Compare` mode semantic checks and timing counters.
10. Run the benchmark corpus, add regression cases for every new output form or
    disagreement, and fix only demonstrated gaps.
11. Make `Process` the default after parity is satisfactory.
12. Remove the temporary comparison/binding path and backend-selection plumbing
    when it no longer provides value.
13. Remove `dep:z3` from the `suggestions` feature and verify the resulting
    process-only build does not link `libz3` (unless `rust-fixpoint` independently
    requests it).

## Non-Goals for the Spike

- A complete SMT-LIB or Z3-output parser.
- General polymorphic function support.
- Supporting arbitrary remaining UIFs through QE.
- Refactoring all Horn formatting before parity is established.
- Changing weak-KVar decomposition, pruning, or candidate-selection semantics.
- Replacing the `rust-fixpoint` binding backend.
- Optimizing process reuse before measuring it.

## Expected Outcome

The control flow in `suggestions.rs` should remain effectively unchanged. The
subprocess backend replaces Z3 AST construction and traversal with SMT-LIB
formatting and a deliberately small result decoder. Most algorithmic code in
`check_validity`, `qe_and_simplify`, and `prune_vacuous` has a direct textual
equivalent.

The main engineering risk is decoding the formulas Z3 actually emits after
`qe; nnf`. Differential comparison, captured query artifacts, and incremental
parser support keep that risk bounded without turning this migration into a
general SMT infrastructure project.

## Spike Results

The focused `flux-demo` comparison reached semantic parity when both backends
used Z3 4.8.12. Matching the binding backend's nested, reverse-order quantifier
construction was necessary because the existing pruning policy is sensitive to
the order of formulas returned by QE. The process decoder also needed to expand
Z3 `let` expressions.

Using the normal `PATH` selected Z3 4.15.3 while the binding backend linked Z3
4.8.12. That version mismatch produced some different but sanity-checked
suggestions; it was not a serialization or decoding failure.

One-shot process execution was substantially slower. On the focused five-query
`Layer::backward` run with Z3 4.8.12, bindings took about 94 ms total while the
process backend took about 1.46 s, roughly 15.5x slower. A full warm
`flux-demo` run measured about 1.76 s with bindings and 5.95 s with the initial
process implementation. Process reuse or batching pruning checks is the next
performance step if this overhead is unacceptable.

After parity testing, the temporary backend selector and binding path were
removed. The `suggestions` feature is process-only and no longer links `libz3`;
`rust-fixpoint` continues to use the Rust `z3` crate independently. The planned
polymorphic `benchmarks/pldi23/src/dotprod.rs` trial remains follow-up work.
