#!/usr/bin/env python3
"""
Script to recursively find and build all lean_proofs directories.

Usage:
    python runlean.py <path>

Example:
    python runlean.py ./lean_bench
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path


def find_lean_proofs_dirs(root_path: Path) -> list[Path]:
    """Recursively find all directories named 'lean_proofs' under root_path."""
    lean_dirs = []
    for dirpath, dirnames, _ in os.walk(root_path):
        if "lean_proofs" in dirnames:
            lean_dirs.append(Path(dirpath) / "lean_proofs")
    return lean_dirs


def run_lake_build(directory: Path) -> tuple[bool, str]:
    """
    Run 'lake build' in the given directory.
    Returns (success, error_output) tuple.
    """
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=directory,
            capture_output=True,
            text=True,
            timeout=300,  # 5 minute timeout per directory
        )
        # Check both return code and stderr for errors
        has_error = result.returncode != 0 or "error" in result.stderr.lower()
        error_output = result.stderr if has_error else ""
        return (not has_error, error_output)
    except subprocess.TimeoutExpired:
        return (False, "Timeout expired (5 minutes)")
    except FileNotFoundError:
        return (False, "lake command not found")
    except Exception as e:
        return (False, str(e))


def main():
    parser = argparse.ArgumentParser(
        description="Recursively run lake build in all lean_proofs directories"
    )
    parser.add_argument(
        "path",
        type=str,
        help="Root path to search for lean_proofs directories",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Print verbose output",
    )
    args = parser.parse_args()

    root_path = Path(args.path).resolve()

    if not root_path.exists():
        print(f"Error: Path '{root_path}' does not exist", file=sys.stderr)
        sys.exit(1)

    if not root_path.is_dir():
        print(f"Error: Path '{root_path}' is not a directory", file=sys.stderr)
        sys.exit(1)

    # Find all lean_proofs directories
    lean_dirs = find_lean_proofs_dirs(root_path)

    if not lean_dirs:
        print(f"No 'lean_proofs' directories found under '{root_path}'")
        sys.exit(0)

    print(f"Found {len(lean_dirs)} lean_proofs directories")
    print("-" * 60)

    # Track results
    visited_count = 0
    error_dirs: list[tuple[Path, str]] = []

    for lean_dir in sorted(lean_dirs):
        visited_count += 1
        relative_path = lean_dir.relative_to(root_path)
        print(f"[{visited_count}/{len(lean_dirs)}] Building: {relative_path} ... ", end="", flush=True)

        success, error_output = run_lake_build(lean_dir)

        if success:
            print("OK")
        else:
            print("ERROR")
            error_dirs.append((lean_dir, error_output))
            if error_output:
                print(f"    Error: {error_output.strip()}")

    # Print summary
    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total directories visited: {visited_count}")
    print(f"Successful builds: {visited_count - len(error_dirs)}")
    print(f"Failed builds: {len(error_dirs)}")

    if error_dirs:
        print()
        print("Directories with errors:")
        for error_dir, error_msg in error_dirs:
            relative_path = error_dir.relative_to(root_path)
            print(f"  - {relative_path}")
            if args.verbose and error_msg:
                # Print first line of error
                first_line = error_msg.strip().split('\n')[0][:100]
                print(f"      {first_line}")

    # Exit with error code if any builds failed
    sys.exit(1 if error_dirs else 0)


if __name__ == "__main__":
    main()
