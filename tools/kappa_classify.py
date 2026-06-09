#!/usr/bin/env python3
"""Parse solve_fixpoint output and classify kappa variable usage.

Each call to solve_fixpoint emits a consecutive pair of lines:
  [solve_fixpoint] Acyclic κ: [...]
  [solve_fixpoint] Cyclic κ:  [...]

This module pairs them up so that files with multiple theorems produce one
classification per invocation rather than one per file.

Classifications:
  none         – both lists empty
  acyclic_only – only acyclic κs present
  cyclic_only  – only cyclic κs present
  both         – acyclic and cyclic κs present

Usage:
    python3 scripts/kappa_classify.py < output.txt
    python3 scripts/kappa_classify.py output.txt
    lake env lean file.lean 2>&1 | python3 scripts/kappa_classify.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ACYCLIC_RE = re.compile(r"\[solve_fixpoint\] Acyclic κ:\s*\[([^\]]*)\]")
CYCLIC_RE  = re.compile(r"\[solve_fixpoint\] Cyclic κ:\s*\[([^\]]*)\]")

# Matches either line so we can scan in document order.
EITHER_RE  = re.compile(
    r"\[solve_fixpoint\] (Acyclic|Cyclic) κ:\s*\[([^\]]*)\]"
)


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def parse_invocations(text: str) -> list[tuple[list[str], list[str]]]:
    """Return one (acyclic, cyclic) pair per solve_fixpoint call.

    Lines are consumed in document order.  Each Acyclic line opens a new
    invocation; the next Cyclic line closes it.  Unmatched lines are grouped
    into a final catch-all invocation so nothing is silently dropped.
    """
    invocations: list[tuple[list[str], list[str]]] = []
    pending_acyclic: list[str] | None = None

    for m in EITHER_RE.finditer(text):
        kind, raw = m.group(1), m.group(2)
        if kind == "Acyclic":
            if pending_acyclic is not None:
                # previous Acyclic had no matching Cyclic
                invocations.append((pending_acyclic, []))
            pending_acyclic = _items(raw)
        else:  # Cyclic
            acyclic = pending_acyclic if pending_acyclic is not None else []
            invocations.append((acyclic, _items(raw)))
            pending_acyclic = None

    if pending_acyclic is not None:
        invocations.append((pending_acyclic, []))

    return invocations


def classify(acyclic: list[str], cyclic: list[str]) -> str:
    if acyclic and cyclic:
        return "both"
    if acyclic:
        return "acyclic_only"
    if cyclic:
        return "cyclic_only"
    return "none"


def main() -> None:
    if len(sys.argv) > 1:
        text = Path(sys.argv[1]).read_text()
    else:
        text = sys.stdin.read()

    invocations = parse_invocations(text)
    if not invocations:
        print("classification : none (no solve_fixpoint calls found)")
        return

    tally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    for i, (acyclic, cyclic) in enumerate(invocations):
        label = classify(acyclic, cyclic)
        tally[label] += 1
        print(f"invocation {i+1:>2} : {label}")
        print(f"  acyclic kappas : {acyclic or '[]'}")
        print(f"  cyclic  kappas : {cyclic  or '[]'}")

    if len(invocations) > 1:
        print("\ntally:")
        for label, n in tally.items():
            if n:
                print(f"  {label:<14} {n}")


if __name__ == "__main__":
    main()
