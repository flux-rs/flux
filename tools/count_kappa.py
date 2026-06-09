#!/usr/bin/env python3
"""Count VC kappa classifications from runlean.py log output.

Each test directory (lean_proofs) can contain multiple VCs, each producing one
solve_fixpoint invocation. This script counts one entry per invocation (VC),
not per test directory. Tests with no solve_fixpoint output contribute one
"none" entry (they have no kvars at all).

Classifications:
  none         – no kvars
  acyclic_only – only acyclic kvars
  cyclic_only  – only cyclic kvars
  both         – both acyclic and cyclic kvars

Usage:
    python3 tools/count_kappa.py lean_bench_log.txt
    python3 tools/runlean.py ./lean_bench 2>&1 | python3 tools/count_kappa.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from kappa_classify import classify, parse_invocations

BUILDING_RE = re.compile(r"\[\d+/\d+\] Building: (.+?) \.\.\.")


def count_from_log(text: str):
    tally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    details: list[tuple[str, int | None, str]] = []

    # Split log into per-test chunks on "Building:" lines
    chunks: list[tuple[str, str]] = []  # (test_path, chunk_text)
    current_vc: str | None = None
    current_lines: list[str] = []

    for line in text.splitlines():
        m = BUILDING_RE.search(line)
        if m:
            if current_vc is not None:
                chunks.append((current_vc, "\n".join(current_lines)))
            current_vc = m.group(1)
            current_lines = [line]
        else:
            current_lines.append(line)

    if current_vc is not None:
        chunks.append((current_vc, "\n".join(current_lines)))


    for test_path, chunk in chunks:
        invocations = parse_invocations(chunk)
        if not invocations:
            # Test produced no solve_fixpoint output — count as one "none" VC
            tally["none"] += 1
            details.append((test_path, None, "none"))
        else:
            for i, (acyclic, cyclic) in enumerate(invocations):
                label = classify(acyclic, cyclic)
                tally[label] += 1
                details.append((test_path, i, label))

    return tally, details


def main() -> None:
    if len(sys.argv) > 1:
        text = Path(sys.argv[1]).read_text()
    else:
        text = sys.stdin.read()

    tally, details = count_from_log(text)
    total = sum(tally.values())

    print(f"{'test':<50} {'vc':>4}  {'classification'}")
    print("-" * 72)
    for test_path, vc_idx, label in details:
        idx_str = "-" if vc_idx is None else str(vc_idx + 1)
        print(f"{test_path:<50} {idx_str:>4}  {label}")

    print()
    print("=" * 72)
    print(f"{'TOTAL VCs:':<25} {total}")
    print("-" * 72)
    for label in ("none", "acyclic_only", "cyclic_only", "both"):
        pct = 100 * tally[label] / total if total else 0
        print(f"  {label:<22} {tally[label]:>4}  ({pct:.1f}%)")


if __name__ == "__main__":
    main()
