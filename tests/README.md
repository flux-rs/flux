# Regression tests

Run with `cargo x test [filename substring]`

- `tests/pos/`: positive tests (pass)
- `tests/neg/`: negative tests (we are testing the errors emitted using `//~ ERROR`)
- `tests/rustfix/`: tests for rustfix (currently this is only for applying suggestions)
- `tests/with_deps/`: same as the above, with `flux_rs` and library specs available.
- `tests/todo/`: todo (excluded from testing)

Use `--suite basic` or `--suite with-deps` to scope to depedency-free tests or `tests/with_deps`.

## Writing rustfix tests

These tests check how `cargo flux fix` applies changes.

Tests are written as
- `test-name.rs`: The test file.
   
   To ensure that we apply the changes, add `//@run-rustfix`,
  `//@rustfix-only-machine-applicable`, and any `//@compile-flags:`.
- `test-name.fixed`: the exact result of applying the fixes.
- `test-name.stderr`: the exact stderr after applying fixes (if omitted, treated as empty).

In many tests, we only care about applying the suggestion,
so add `//@normalize-stderr-test: "(?s).*" -> ""` to skip diagnostic-text snapshots.
What this does is turn stderr into the empty string --- if you do this, you can then
skip adding a `.stderr`.

Tests requiring `flux_rs` or extern specs live in `tests/with_deps/rustfix/` and use
the same conventions.

### Generating expected tests

You can generate the `.fixed` and `.stderr` files if your test is on behavior that
currently works using `--bless`, e.g. `cargo x test my-test --bless`.
