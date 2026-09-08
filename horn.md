# Dumping constraints as SMT-LIB Horn clauses

`-Fdump-smt-horn=DIR` writes one `.smt2` file per fixpoint query with at least one kvar, plus
`DIR/_skipped.log` for queries the formatter could not encode. The directory is not cleared
between runs.

## Generate

This repo's test suite (`FLUX_POS_ONLY=1` skips the neg suite; `FLUXFLAGS` is forwarded to every
test invocation):

```bash
FLUX_POS_ONLY=1 FLUXFLAGS="-Fdump-smt-horn=/tmp/horn" cargo xtask test
```

Another crate, via `cargo flux`:

```bash
FLUXFLAGS="-Fdump-smt-horn=/tmp/horn" cargo flux
```

A single file (`cargo xtask run` does not read `FLUXFLAGS`, so pass the flag through):

```bash
cargo xtask run tests/tests/pos/surface/test01.rs -- -Fdump-smt-horn=/tmp/horn
```

## Report

```bash
./horn_report.py /tmp/horn -T 15 --dedup 
```
