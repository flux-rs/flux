#!/usr/bin/env python3
"""Parse lean_bench_log.txt and VC files, export per-VC stats as JSON.

Each VC file under lean_proofs/LeanProofs/Flux/VC/ is one entry.
Trivial = body of last def is just 'True'.
Classification = from solve_fixpoint kappa output in the log.
Failed = explicit error line for that VC's proof file, or whole test timed
         out / errored and the VC has no kappa output at all.

Output (to stdout):
    JSON array: [{"suite": "Flux lean-bench", "vcs": [...]}]

Usage:
    python3 tools/export_lean_bench_stats.py
    python3 tools/export_lean_bench_stats.py <lean_bench_root> <log_file>
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT      = Path(__file__).resolve().parent.parent
DEFAULT_BENCH  = REPO_ROOT / "tests" / "lean_bench"
DEFAULT_LOG    = REPO_ROOT / "lean_bench_log.txt"

BUILDING_RE = re.compile(r"^\[(\d+)/(\d+)\] Building: (.+?) \.\.\. (OK|ERROR)$")
ACYCLIC_RE  = re.compile(
    r"info: .*/(\w+)Proof\.lean:\d+:\d+: \[solve_fixpoint\] Acyclic κ:\s*\[([^\]]*)\]"
)
CYCLIC_RE   = re.compile(r"\[solve_fixpoint\] Cyclic κ:\s*\[([^\]]*)\]")
ERROR_RE    = re.compile(r"error: LeanProofs/User/Proof/(\w+)Proof\.lean:")
DEF_RE      = re.compile(r"^def \S+ :=\s*$|^def \S+ := (.+)", re.MULTILINE)


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def classify(acyclic: list[str], cyclic: list[str]) -> str:
    if acyclic and cyclic:
        return "both"
    if acyclic:
        return "acyclic_only"
    if cyclic:
        return "cyclic_only"
    return "none"


def is_trivially_true(path: Path) -> bool:
    text = path.read_text(encoding="utf-8", errors="replace")
    matches = list(DEF_RE.finditer(text))
    if not matches:
        return False
    last = matches[-1]
    if last.group(1) is not None:
        return last.group(1).strip() == "True"
    body = re.split(r"\bend\b", text[last.end():], maxsplit=1)[0].strip()
    return body == "True"


def parse_chunk(lines: list[str]) -> tuple[dict[str, str], set[str]]:
    """Return (kappa_by_vc, failed_vcs) for one test chunk."""
    kappa_by_vc: dict[str, str] = {}
    failed_vcs: set[str] = set()

    i = 0
    while i < len(lines):
        m = ACYCLIC_RE.search(lines[i])
        if m:
            vc = m.group(1)
            acyclic = _items(m.group(2))
            cyclic: list[str] = []
            if i + 1 < len(lines):
                cm = CYCLIC_RE.search(lines[i + 1])
                if cm:
                    cyclic = _items(cm.group(1))
                    i += 1
            kappa_by_vc[vc] = classify(acyclic, cyclic)
        m2 = ERROR_RE.search(lines[i])
        if m2:
            failed_vcs.add(m2.group(1))
        i += 1

    return kappa_by_vc, failed_vcs


def main() -> None:
    bench_root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_BENCH
    log_path   = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else DEFAULT_LOG

    if not log_path.exists():
        print(f"error: log not found: {log_path}", file=sys.stderr)
        sys.exit(1)
    if not bench_root.is_dir():
        print(f"error: lean_bench not found: {bench_root}", file=sys.stderr)
        sys.exit(1)

    # Split log into per-test chunks.
    chunks: list[tuple[str, bool, list[str]]] = []  # (test_rel_path, chunk_failed, lines)
    current_rel: str | None = None
    current_failed = False
    current_lines: list[str] = []

    for line in log_path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = BUILDING_RE.match(line)
        if m:
            if current_rel is not None:
                chunks.append((current_rel, current_failed, current_lines))
            # test_rel: strip trailing "/lean_proofs"
            raw_path = m.group(3)
            current_rel = raw_path.removesuffix("/lean_proofs")
            current_failed = m.group(4) == "ERROR"
            current_lines = []
        else:
            current_lines.append(line)

    if current_rel is not None:
        chunks.append((current_rel, current_failed, current_lines))

    # Build lookup: test_rel -> (kappa_by_vc, failed_vcs, chunk_failed)
    chunk_map: dict[str, tuple[dict[str, str], set[str], bool]] = {}
    for rel, chunk_failed, lines in chunks:
        kappa_by_vc, failed_vcs = parse_chunk(lines)
        chunk_map[rel] = (kappa_by_vc, failed_vcs, chunk_failed)

    # Walk all VC files.
    vcs: list[dict] = []
    for vc_path in sorted(bench_root.rglob("LeanProofs/Flux/VC/*.lean")):
        # Derive test_rel from path.
        try:
            parts = vc_path.relative_to(bench_root).parts
            lp_idx = parts.index("lean_proofs")
            test_rel = "/".join(parts[:lp_idx])
        except (ValueError, KeyError):
            continue

        vc_name = vc_path.stem
        trivial = is_trivially_true(vc_path)
        kappa_by_vc, failed_vcs, chunk_failed = chunk_map.get(test_rel, ({}, set(), False))

        kappa = kappa_by_vc.get(vc_name, "none")

        # A VC is failed if it has an explicit error line, or the whole test
        # failed and it has no kappa output (never reached solve_fixpoint).
        failed = vc_name in failed_vcs or (chunk_failed and vc_name not in kappa_by_vc)

        vcs.append({"name": f"{test_rel}/{vc_name}", "trivial": trivial,
                    "kappa": kappa, "failed": failed})

    time_path = log_path.parent / "lean_bench.time"
    suite: dict = {"suite": "Flux lean-bench", "vcs": vcs}
    try:
        suite["time_ms"] = int(time_path.read_text().strip())
    except Exception:
        pass

    print(json.dumps([suite], indent=2))


if __name__ == "__main__":
    main()
