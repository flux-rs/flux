#!/bin/bash
# Script to generate lean benchmarks and run them

set -e

echo "=== Step 1: Running cargo x test --emit-lean ==="
cargo x test --emit-lean

echo ""
echo "=== Step 2: Running lean builds ==="
python3 tools/runlean.py tests/lean_bench > lean_bench_log.txt 2>&1

echo ""
echo "=== Done! Results in lean_bench_log.txt ==="
