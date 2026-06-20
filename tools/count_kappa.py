#!/usr/bin/env python3
"""Count VC kappa classifications from build log output.

Works with logs from both runlean.py modes:

  Per-test log  (runlean.py <lean_bench_root>):
    One chunk per test, delimited by "[N/M] Building: path ..." lines.

  Merged log  (runlean.py --merged <dir>):
    Single lake build output; VCs identified by proof-file paths in info lines.

Classifications:
  none         – no kvars
  acyclic_only – only acyclic kvars
  cyclic_only  – only cyclic kvars
  both         – both acyclic and cyclic kvars

Usage:
    python3 tools/count_kappa.py lean_bench_log.txt
    python3 tools/count_kappa.py --merged lean_bench_log.txt
    python3 tools/runlean.py ./lean_bench 2>&1 | python3 tools/count_kappa.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from kappa_classify import classify, parse_invocations

# Per-test log delimiter.
BUILDING_RE = re.compile(r"\[\d+/\d+\] Building: (.+?) \.\.\.")

# Merged log: extract vc_name from info lines on proof files.
MERGED_PROOF_RE = re.compile(
    r"^info:\s+\S+/User/Proof/(\w+)Proof\.lean:\d+:\d+:\s+(.*)"
)


# ---------------------------------------------------------------------------
# Per-test mode (original)
# ---------------------------------------------------------------------------

def count_pertest(text: str):
    tally: dict[str, int] = {
        "none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0
    }
    details: list[tuple[str, int | None, str]] = []

    chunks: list[tuple[str, str]] = []
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
            tally["none"] += 1
            details.append((test_path, None, "none"))
        else:
            for i, (acyclic, cyclic) in enumerate(invocations):
                label = classify(acyclic, cyclic)
                tally[label] += 1
                details.append((test_path, i, label))

    return tally, details


# ---------------------------------------------------------------------------
# Merged mode
# ---------------------------------------------------------------------------

def count_merged(text: str):
    """
    Parse a merged-project lake build log.

    Each VC is identified by its proof file path in info lines.
    Acyclic/Cyclic κ pairs are matched per VC in document order.
    """
    tally: dict[str, int] = {
        "none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0
    }
    details: list[tuple[str, int | None, str]] = []

    # Per-VC: list of (acyclic, cyclic) invocation pairs.
    vc_invocations: dict[str, list[tuple[list[str], list[str]]]] = {}
    pending_acyclic: dict[str, list[str]] = {}

    def _items(raw: str) -> list[str]:
        return [k.strip() for k in raw.split(",") if k.strip()]

    for line in text.splitlines():
        m = MERGED_PROOF_RE.match(line)
        if not m:
            continue
        vc_name, message = m.group(1), m.group(2)

        if "[solve_fixpoint] Acyclic" in message:
            raw = re.search(r"\[([^\]]*)\]", message)
            pending_acyclic[vc_name] = _items(raw.group(1)) if raw else []

        elif "[solve_fixpoint] Cyclic" in message:
            raw = re.search(r"\[([^\]]*)\]", message)
            cyclic = _items(raw.group(1)) if raw else []
            acyclic = pending_acyclic.pop(vc_name, [])
            vc_invocations.setdefault(vc_name, []).append((acyclic, cyclic))

        elif "fusion: eliminated" in message:
            # fusion counts as an acyclic invocation with no solve_fixpoint pair
            vc_invocations.setdefault(vc_name, []).append((["fusion"], []))

    # Flush unmatched Acyclic lines.
    for vc_name, acyclic in pending_acyclic.items():
        vc_invocations.setdefault(vc_name, []).append((acyclic, []))

    for vc_name, invocations in sorted(vc_invocations.items()):
        if not invocations:
            tally["none"] += 1
            details.append((vc_name, None, "none"))
        else:
            for i, (acyclic, cyclic) in enumerate(invocations):
                label = classify(acyclic, cyclic)
                tally[label] += 1
                details.append((vc_name, i, label))

    return tally, details


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def _print_results(tally, details) -> None:
    print(f"{'test/vc':<55} {'#':>3}  {'classification'}")
    print("-" * 76)
    for name, vc_idx, label in details:
        idx_str = "-" if vc_idx is None else str(vc_idx + 1)
        print(f"{name:<55} {idx_str:>3}  {label}")

    total = sum(tally.values())
    print()
    print("=" * 76)
    print(f"{'TOTAL VCs:':<25} {total}")
    print("-" * 76)
    for label in ("none", "acyclic_only", "cyclic_only", "both"):
        pct = 100 * tally[label] / total if total else 0
        print(f"  {label:<22} {tally[label]:>4}  ({pct:.1f}%)")


def main() -> None:
    merged_mode = "--merged" in sys.argv
    argv = [a for a in sys.argv[1:] if a != "--merged"]

    if argv:
        text = Path(argv[0]).read_text()
    else:
        text = sys.stdin.read()

    if merged_mode:
        tally, details = count_merged(text)
    else:
        # Auto-detect: if log contains the per-test "Building:" header, use that mode.
        if BUILDING_RE.search(text):
            tally, details = count_pertest(text)
        else:
            tally, details = count_merged(text)

    _print_results(tally, details)


if __name__ == "__main__":
    main()
