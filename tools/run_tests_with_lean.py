#!/usr/bin/env python3
"""
Script to run Flux tests with lean emission enabled.

This replicates the functionality of `run_tests_with_lean_emit` in compiletest.rs,
but as a standalone Python script.

Usage:
    python run_tests_with_lean.py [options] [filters...]

Examples:
    python run_tests_with_lean.py                      # Run all tests in tests/pos/
    python run_tests_with_lean.py test00               # Run tests matching "test00"
    python run_tests_with_lean.py surface/test00       # Run tests matching "surface/test00"
    python run_tests_with_lean.py --pos-path tests/pos surface  # Custom pos path
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path


def find_rust_tests(pos_path: Path, filters: list[str]) -> list[Path]:
    """Find all .rs test files under pos_path, optionally filtered."""
    test_files = []
    for root, _, files in os.walk(pos_path):
        for file in files:
            if file.endswith(".rs"):
                test_path = Path(root) / file
                # Apply filters if any
                if filters:
                    path_str = str(test_path)
                    if not any(f in path_str for f in filters):
                        continue
                test_files.append(test_path)
    return sorted(test_files)


def run_test_with_lean(
    test_path: Path,
    pos_path: Path,
    lean_bench_dir: Path,
    verbose: bool = False,
) -> tuple[bool, str]:
    """
    Run a single test with lean emission enabled.
    Returns (success, error_message) tuple.
    """
    # Get the relative path from tests/pos/ (e.g., "surface/test00.rs")
    rel_path = test_path.relative_to(pos_path)

    # Create lean output dir: ./lean_bench/<path>/<to>/<file>/
    # e.g., for tests/pos/surface/test00.rs -> ./lean_bench/surface/test00/
    lean_dir = lean_bench_dir
    if rel_path.parent != Path("."):
        lean_dir = lean_dir / rel_path.parent
    lean_dir = lean_dir / rel_path.stem

    # Create the directory if it doesn't exist
    lean_dir.mkdir(parents=True, exist_ok=True)

    # Run cargo x run with lean flags
    cmd = [
        "cargo", "x", "run",
        str(test_path),
        "--",
        "-Flean=emit",
        f"-Flean-dir={lean_dir}",
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=300,  # 5 minute timeout
        )

        if result.returncode != 0:
            error_msg = result.stderr or result.stdout or f"Exit code: {result.returncode}"
            return (False, error_msg)

        return (True, "")

    except subprocess.TimeoutExpired:
        return (False, "Timeout expired (5 minutes)")
    except Exception as e:
        return (False, str(e))


def main():
    parser = argparse.ArgumentParser(
        description="Run Flux tests with lean emission enabled"
    )
    parser.add_argument(
        "filters",
        nargs="*",
        help="Filter tests by substring (tests must contain at least one filter)",
    )
    parser.add_argument(
        "--pos-path",
        type=str,
        default="tests/tests/pos",
        help="Path to the pos tests directory (default: tests/tests/pos)",
    )
    parser.add_argument(
        "--lean-bench-dir",
        type=str,
        default="tests/lean_bench",
        help="Output directory for lean benchmarks (default: tests/lean_bench)",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Print verbose output including error details",
    )
    parser.add_argument(
        "--continue-on-error",
        action="store_true",
        help="Continue running tests even if some fail (default behavior)",
    )
    args = parser.parse_args()

    pos_path = Path(args.pos_path).resolve()
    lean_bench_dir = Path(args.lean_bench_dir).resolve()

    if not pos_path.exists():
        print(f"Error: Path '{pos_path}' does not exist", file=sys.stderr)
        sys.exit(1)

    if not pos_path.is_dir():
        print(f"Error: Path '{pos_path}' is not a directory", file=sys.stderr)
        sys.exit(1)

    # Find all test files
    test_files = find_rust_tests(pos_path, args.filters)

    if not test_files:
        if args.filters:
            print(f"No test files found matching filters: {args.filters}")
        else:
            print(f"No test files found under '{pos_path}'")
        sys.exit(0)

    print(f"Found {len(test_files)} test files")
    print("-" * 60)

    # Track results
    failures: list[tuple[Path, str]] = []
    successes = 0

    for i, test_path in enumerate(test_files, 1):
        rel_path = test_path.relative_to(pos_path)
        print(f"[{i}/{len(test_files)}] Running: {rel_path} ... ", end="", flush=True)

        success, error_msg = run_test_with_lean(
            test_path, pos_path, lean_bench_dir, args.verbose
        )

        if success:
            print("OK")
            successes += 1
        else:
            print("ERROR")
            failures.append((test_path, error_msg))
            if args.verbose and error_msg:
                # Print first few lines of error
                error_lines = error_msg.strip().split('\n')[:5]
                for line in error_lines:
                    print(f"    {line[:100]}")

    # Print summary
    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total tests run: {len(test_files)}")
    print(f"Passed: {successes}")
    print(f"Failed: {len(failures)}")

    if failures:
        print()
        print("Failed tests:")
        for failed_path, error_msg in failures:
            rel_path = failed_path.relative_to(pos_path)
            print(f"  - {rel_path}")
            if args.verbose and error_msg:
                first_line = error_msg.strip().split('\n')[0][:80]
                print(f"      {first_line}")
        print("=" * 60)

    # Exit with error code if any tests failed
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
