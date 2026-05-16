#!/usr/bin/env bash
# scripts/noncut-compare.sh
#
# For each currently-failing pos test (the ones that break when Flux performs
# its non-cut KVar substitution on the local constraint), run flux with
# FLUX_NONCUT_COMPARE=<dir> set so each task dumps a side-by-side comparison of
# Flux's local non-cut KVar solutions vs. fixpoint's non-cut solutions.
#
# Note: with FLUX_NONCUT_COMPARE set, the encoder *skips* its local
# `elim_non_cut_kvars` step and ships the un-eliminated constraint to fixpoint
# (so fixpoint will report its own non-cut solutions in `nonCutsSolution`).
# This means tests that "fail when we substitute" will likely pass under this
# script — that's fine; we're using the script only to dump comparisons, not
# to verify status.
#
# Usage:
#   ./scripts/noncut-compare.sh [output-dir]
#
# Default output directory: /tmp/noncut-compare
#
# After it finishes, inspect:
#   ls <dir>/                      # one subdirectory per test
#   ls <dir>/<test>/               # one .txt per task that had non-cut kvars
#   less <dir>/<test>/<task>.txt
#
# Each per-task file lists, for every non-cut kvar reported by either side:
#   - flux's local solution (per-cube cube-pred strings, ∃-bound)
#   - fixpoint's nonCutsSolution

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT_DIR="${1:-/tmp/noncut-compare}"
SUMMARY="$OUT_DIR/_SUMMARY.txt"

# The 18 currently-failing pos tests on the Step 2 work branch.
TESTS=(
  pos/enums/list00.rs
  pos/enums/list01.rs
  pos/lifetimes/list_mut_ref.rs
  pos/structs/issue-578.rs
  pos/surface/closure02.rs
  pos/surface/ghostcell00.rs
  pos/surface/heapsort.rs
  pos/surface/issue-431.rs
  pos/surface/iter01.rs
  pos/surface/join01.rs
  pos/surface/join04.rs
  pos/surface/kmeans.rs
  pos/surface/kmp_overflow.rs
  pos/surface/kmp.rs
  pos/surface/polymorphic_qualifier.rs
  pos/surface/ref_cell00.rs
  pos/surface/simplex.rs
  pos/surface/test01.rs
)

cd "$REPO_ROOT"

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"
: > "$SUMMARY"

echo "[noncut-compare] dumping into $OUT_DIR"

for t in "${TESTS[@]}"; do
  TEST_NAME="${t//\//_}"
  TEST_NAME="${TEST_NAME%.rs}"
  TEST_OUT_DIR="$OUT_DIR/$TEST_NAME"
  mkdir -p "$TEST_OUT_DIR"

  # Use the test path as the cargo-test filter substring. Picks exactly the
  # one test (and possibly nothing else with the same suffix).
  FILTER="${t%.rs}"

  echo "[noncut-compare] $t"
  FLUX_NONCUT_COMPARE="$TEST_OUT_DIR" \
    cargo xtask test "$FILTER" \
    >"$TEST_OUT_DIR/_stdout.txt" 2>"$TEST_OUT_DIR/_stderr.txt"
  RC=$?

  N_DUMPS=$(find "$TEST_OUT_DIR" -maxdepth 1 -name '*.txt' ! -name '_*' 2>/dev/null | wc -l)
  printf "  %-50s rc=%d  task_dumps=%d\n" "$t" "$RC" "$N_DUMPS" | tee -a "$SUMMARY"
done

echo
echo "[noncut-compare] done. summary in $SUMMARY"
echo "[noncut-compare] inspect: ls $OUT_DIR/<test>/"
