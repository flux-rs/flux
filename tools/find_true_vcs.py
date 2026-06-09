#!/usr/bin/env python3
"""Find VC files whose statement is just `True`.

A VC file lives at:
  tests/lean_bench/<test_path>/lean_proofs/LeanProofs/Flux/VC/<Name>.lean

A VC is "just True" when the body of the last `def` in the file is exactly
`True` (ignoring whitespace and a trailing `end F`).

Usage:
    python3 tools/find_true_vcs.py [lean_bench_root]

Defaults to tests/lean_bench relative to the repo root.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DEF_RE = re.compile(r"^def \S+ :=\s*$|^def \S+ := (.+)", re.MULTILINE)


def is_true_vc(path: Path) -> bool:
    text = path.read_text()

    # Find the last `def` in the file.
    matches = list(DEF_RE.finditer(text))
    if not matches:
        return False

    last = matches[-1]
    # Inline form: def Name := True
    if last.group(1) is not None:
        return last.group(1).strip() == "True"

    # Multi-line form: body starts on the next line, ends at `end F` or EOF.
    body_start = last.end()
    rest = text[body_start:]
    # Strip trailing `end F` block and surrounding whitespace.
    body = re.split(r"\bend\b", rest, maxsplit=1)[0].strip()
    return body == "True"


def main() -> None:
    if len(sys.argv) > 1:
        root = Path(sys.argv[1]).resolve()
    else:
        # Default: repo_root/tests/lean_bench
        root = Path(__file__).resolve().parent.parent / "tests" / "lean_bench"

    vc_files = sorted(root.rglob("LeanProofs/Flux/VC/*.lean"))

    if not vc_files:
        print(f"No VC files found under {root}", file=sys.stderr)
        sys.exit(1)

    true_vcs: list[Path] = []
    nontrue_vcs: list[Path] = []

    for f in vc_files:
        (true_vcs if is_true_vc(f) else nontrue_vcs).append(f)

    total = len(vc_files)
    n_true = len(true_vcs)

    print(f"True VCs ({n_true}/{total}):")
    for f in true_vcs:
        # Print relative to lean_bench root for readability
        try:
            rel = f.relative_to(root)
        except ValueError:
            rel = f
        print(f"  {rel}")

    print()
    print(f"Total VCs : {total}")
    print(f"True      : {n_true}  ({100*n_true/total:.1f}%)")
    print(f"Non-True  : {total - n_true}  ({100*(total-n_true)/total:.1f}%)")


if __name__ == "__main__":
    main()
