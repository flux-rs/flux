#!/bin/bash
# Script to generate lean benchmarks and run them via a merged Lake project.

set -e

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MERGED_DIR="${REPO_ROOT}/lean_bench_merged"

echo "=== Step 1: Flux-only timing (no lean emission) ==="
cargo x lean-bench --flux-only "$@" || true
# Writes flux_bench.time to cwd.

echo ""
echo "=== Step 2: Generating lean proofs ==="
cargo x lean-bench || true

echo ""
echo "=== Step 3: Merging lean_proofs projects ==="
rm -rf "$MERGED_DIR"
bash "${REPO_ROOT}/tools/merge_projects.sh" \
    "${REPO_ROOT}/tests/lean_bench" \
    "$MERGED_DIR"

echo ""
echo "=== Step 4: Running lean build on merged project ==="
# Writes lean_bench.time (wall-clock of lake build) to cwd.
python3 "${REPO_ROOT}/tools/runlean.py" --merged "$MERGED_DIR" \
    > "${REPO_ROOT}/lean_bench_log.txt" 2>&1 || true

echo ""
echo "=== Done! Results in lean_bench_log.txt ==="
