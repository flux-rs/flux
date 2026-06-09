#!/usr/bin/env python3
"""Count non-True VCs that are successfully proven by solve_fixpoint.

A VC is "successfully proven by solve_fixpoint" if the log contains:
  info: LeanProofs/User/Proof/<VcName>Proof.lean:...: [solve_fixpoint] Acyclic κ: ...
for its corresponding test project.

A VC is "just True" when the body of the last `def` in the Flux/VC/<Name>.lean file
is exactly `True` (same logic as find_true_vcs.py).

Usage:
    python3 tools/count_fixpoint_provable.py [lean_bench_root [log_file]]

Defaults:
  lean_bench_root = tests/lean_bench (relative to repo root)
  log_file        = lean_bench_log.txt (relative to repo root)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DEF_RE = re.compile(r"^def \S+ :=\s*$|^def \S+ := (.+)", re.MULTILINE)
BUILD_RE = re.compile(r"^\[\d+/\d+\] Building: (.+)/lean_proofs \.\.\.")
ACYCLIC_RE = re.compile(
    r"^\s+info: (LeanProofs/User/Proof/\S+\.lean):\d+:\d+: \[solve_fixpoint\] Acyclic κ:"
)
ERROR_RE = re.compile(r"^\s+error: (LeanProofs/User/Proof/\S+\.lean):")


def is_true_vc(path: Path) -> bool:
    text = path.read_text()
    matches = list(DEF_RE.finditer(text))
    if not matches:
        return False
    last = matches[-1]
    if last.group(1) is not None:
        return last.group(1).strip() == "True"
    body_start = last.end()
    rest = text[body_start:]
    body = re.split(r"\bend\b", rest, maxsplit=1)[0].strip()
    return body == "True"


def parse_log(log_path: Path) -> dict[str, set[str]]:
    """Return {test_path: set of proof filenames} that have Acyclic κ AND no error lines."""
    acyclic: dict[str, set[str]] = {}
    errored: dict[str, set[str]] = {}
    current: str | None = None

    for line in log_path.read_text().splitlines():
        m = BUILD_RE.match(line)
        if m:
            current = m.group(1)
            acyclic.setdefault(current, set())
            errored.setdefault(current, set())
            continue
        if current is None:
            continue
        m = ACYCLIC_RE.match(line)
        if m:
            acyclic[current].add(Path(m.group(1)).name)
            continue
        m = ERROR_RE.match(line)
        if m:
            errored[current].add(Path(m.group(1)).name)

    # A proof is considered solved only if solve_fixpoint ran (Acyclic κ logged)
    # and no error was emitted for that proof file.
    return {
        tp: acyclic[tp] - errored.get(tp, set())
        for tp in acyclic
    }


def proof_name(vc_path: Path) -> str:
    """'Foo.lean' -> 'FooProof.lean'"""
    return vc_path.stem + "Proof.lean"


def test_path_for_vc(vc_path: Path, lean_bench_root: Path) -> str:
    """Extract the test_path (e.g. 'abstract_refinements/test00') from a VC file path."""
    # vc_path: .../lean_bench/<test_path>/lean_proofs/LeanProofs/Flux/VC/Foo.lean
    parts = vc_path.relative_to(lean_bench_root).parts
    # parts[0] and parts[1] make up the test_path (category/testname)
    # but some may be deeper — find the 'lean_proofs' anchor
    try:
        lp_idx = parts.index("lean_proofs")
    except ValueError:
        return str(vc_path)
    return "/".join(parts[:lp_idx])


def main() -> None:
    repo_root = Path(__file__).resolve().parent.parent

    lean_bench_root = (
        Path(sys.argv[1]).resolve() if len(sys.argv) > 1
        else repo_root / "tests" / "lean_bench"
    )
    log_path = (
        Path(sys.argv[2]).resolve() if len(sys.argv) > 2
        else repo_root / "lean_bench_log.txt"
    )

    vc_files = sorted(lean_bench_root.rglob("LeanProofs/Flux/VC/*.lean"))
    if not vc_files:
        print(f"No VC files found under {lean_bench_root}", file=sys.stderr)
        sys.exit(1)

    if not log_path.exists():
        print(f"Log file not found: {log_path}", file=sys.stderr)
        sys.exit(1)

    proven_by_fixpoint = parse_log(log_path)

    total = len(vc_files)
    true_vcs: list[Path] = []
    nontrue_provable: list[Path] = []
    nontrue_not_provable: list[Path] = []

    for f in vc_files:
        if is_true_vc(f):
            true_vcs.append(f)
            continue
        tp = test_path_for_vc(f, lean_bench_root)
        pname = proof_name(f)
        proven_set = proven_by_fixpoint.get(tp, set())
        if pname in proven_set:
            nontrue_provable.append(f)
        else:
            nontrue_not_provable.append(f)

    n_true = len(true_vcs)
    n_provable = len(nontrue_provable)
    n_not_provable = len(nontrue_not_provable)
    n_nontrue = n_provable + n_not_provable

    print(f"Non-True VCs provable by solve_fixpoint ({n_provable}/{n_nontrue}):")
    for f in nontrue_provable:
        try:
            rel = f.relative_to(lean_bench_root)
        except ValueError:
            rel = f
        print(f"  {rel}")

    print()
    print(f"Non-True VCs NOT provable by solve_fixpoint ({n_not_provable}/{n_nontrue}):")
    for f in nontrue_not_provable:
        try:
            rel = f.relative_to(lean_bench_root)
        except ValueError:
            rel = f
        print(f"  {rel}")

    print()
    print(f"Total VCs                          : {total}")
    print(f"True VCs                           : {n_true}  ({100*n_true/total:.1f}%)")
    print(f"Non-True VCs                       : {n_nontrue}  ({100*n_nontrue/total:.1f}%)")
    print(f"  Provable by solve_fixpoint        : {n_provable}  ({100*n_provable/n_nontrue:.1f}% of non-True)")
    print(f"  Not provable by solve_fixpoint    : {n_not_provable}  ({100*n_not_provable/n_nontrue:.1f}% of non-True)")


if __name__ == "__main__":
    main()
