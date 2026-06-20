#!/usr/bin/env python3
"""Parse lean build output and VC files; export per-VC stats as JSON.

Two modes:

  Per-test mode (original):
    python3 export_lean_bench_stats.py [lean_bench_root [log_file]]
    Reads lean_bench_log.txt produced by `runlean.py <lean_bench_root>`.
    VC files are under <lean_bench_root>/**/LeanProofs/Flux/VC/*.lean.

  Merged mode:
    python3 export_lean_bench_stats.py --merged <merged_dir> [--log <log>]
    Reads the log produced by `runlean.py --merged <merged_dir>`.
    VC files are under <merged_dir>/**/<Cat>/<Test>/Flux/VC/*.lean.

Output (stdout): JSON array: [{"suite": "Flux lean-bench", "vcs": [...]}]

Each VC entry:
  {
    "name":    "<test_id>/<VCName>",
    "trivial": bool,          # body of last def is True
    "kappa":   "none"|"acyclic_only"|"cyclic_only"|"both",
    "failed":  bool,
  }
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT     = Path(__file__).resolve().parent.parent
DEFAULT_BENCH = REPO_ROOT / "tests" / "lean_bench"
DEFAULT_LOG   = REPO_ROOT / "lean_bench_log.txt"

DEF_RE = re.compile(r"^def \S+ :=\s*$|^def \S+ := (.+)", re.MULTILINE)


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

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


def classify(acyclic: list[str], cyclic: list[str]) -> str:
    if acyclic and cyclic:
        return "both"
    if acyclic:
        return "acyclic_only"
    if cyclic:
        return "cyclic_only"
    return "none"


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def load_timing(log_dir: Path) -> dict:
    result = {}
    for key, fname in [("time_ms", "lean_bench.time"),
                       ("flux_time_ms", "flux_bench.time")]:
        try:
            result[key] = int((log_dir / fname).read_text().strip())
        except Exception:
            pass
    return result


# ---------------------------------------------------------------------------
# Per-test mode (original)
# ---------------------------------------------------------------------------

BUILDING_RE = re.compile(r"^\[(\d+)/(\d+)\] Building: (.+?) \.\.\. (OK|ERROR)$")
ACYCLIC_RE_PT = re.compile(
    r"info: .*/(\w+)Proof\.lean:\d+:\d+: \[solve_fixpoint\] Acyclic κ:\s*\[([^\]]*)\]"
)
CYCLIC_RE_PT  = re.compile(r"\[solve_fixpoint\] Cyclic κ:\s*\[([^\]]*)\]")
FUSION_RE_PT  = re.compile(
    r"info: .*/(\w+)Proof\.lean:\d+:\d+: fusion: eliminated \d+ acyclic κ"
)
ERROR_RE_PT   = re.compile(r"error: LeanProofs/User/Proof/(\w+)Proof\.lean:")


def parse_pertest_chunk(lines: list[str]) -> tuple[dict[str, str], set[str]]:
    """Return (kappa_by_vc, failed_vcs) for one test chunk."""
    kappa_by_vc: dict[str, str] = {}
    failed_vcs: set[str] = set()
    fusion_acyclic: set[str] = {
        m.group(1)
        for line in lines
        for m in [FUSION_RE_PT.search(line)] if m
    }
    i = 0
    while i < len(lines):
        m = ACYCLIC_RE_PT.search(lines[i])
        if m:
            vc = m.group(1)
            acyclic = _items(m.group(2)) or (["fusion"] if vc in fusion_acyclic else [])
            cyclic: list[str] = []
            if i + 1 < len(lines):
                cm = CYCLIC_RE_PT.search(lines[i + 1])
                if cm:
                    cyclic = _items(cm.group(1))
                    i += 1
            kappa_by_vc[vc] = classify(acyclic, cyclic)
        m2 = ERROR_RE_PT.search(lines[i])
        if m2:
            failed_vcs.add(m2.group(1))
        i += 1
    return kappa_by_vc, failed_vcs


def run_pertest(bench_root: Path, log_path: Path) -> list[dict]:
    chunks: list[tuple[str, bool, list[str]]] = []
    current_rel: str | None = None
    current_failed = False
    current_lines: list[str] = []

    for line in log_path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = BUILDING_RE.match(line)
        if m:
            if current_rel is not None:
                chunks.append((current_rel, current_failed, current_lines))
            current_rel = m.group(3).removesuffix("/lean_proofs")
            current_failed = m.group(4) == "ERROR"
            current_lines = []
        else:
            current_lines.append(line)
    if current_rel is not None:
        chunks.append((current_rel, current_failed, current_lines))

    chunk_map: dict[str, tuple[dict[str, str], set[str], bool]] = {}
    for rel, chunk_failed, lines in chunks:
        kappa_by_vc, failed_vcs = parse_pertest_chunk(lines)
        chunk_map[rel] = (kappa_by_vc, failed_vcs, chunk_failed)

    vcs: list[dict] = []
    for vc_path in sorted(bench_root.rglob("LeanProofs/Flux/VC/*.lean")):
        try:
            parts = vc_path.relative_to(bench_root).parts
            lp_idx = parts.index("lean_proofs")
            test_rel = "/".join(parts[:lp_idx])
        except (ValueError, KeyError):
            continue

        vc_name = vc_path.stem
        trivial = is_trivially_true(vc_path)
        kappa_by_vc, failed_vcs, chunk_failed = chunk_map.get(
            test_rel, ({}, set(), False)
        )
        kappa = kappa_by_vc.get(vc_name, "none")
        failed = vc_name in failed_vcs or (
            chunk_failed and vc_name not in kappa_by_vc
        )
        vcs.append({
            "name": f"{test_rel}/{vc_name}",
            "trivial": trivial,
            "kappa": kappa,
            "failed": failed,
        })
    return vcs


# ---------------------------------------------------------------------------
# Merged mode
# ---------------------------------------------------------------------------

LEAN_LINE_RE = re.compile(
    r"^(?:info|error):\s+(\S+/User/Proof/(\w+)Proof\.lean):\d+:\d+:\s+(.*)"
)
LAKE_FAIL_RE = re.compile(r"^✖\s+\[\d+/\d+\]\s+Building\s+([\w.]+)")
ACYCLIC_RE_M = re.compile(r"\[solve_fixpoint\] Acyclic κ:\s*\[([^\]]*)\]")
CYCLIC_RE_M  = re.compile(r"\[solve_fixpoint\] Cyclic κ:\s*\[([^\]]*)\]")


def parse_merged_log(log_path: Path) -> dict[str, dict]:
    """
    Parse the raw `lake build` log from the merged project.

    Returns dict keyed by vc_name:
      {"failed": bool, "acyclic": [...], "cyclic": [...], "fusion": bool}
    """
    vcs: dict[str, dict] = {}

    def _get(name: str) -> dict:
        if name not in vcs:
            vcs[name] = {"failed": False, "acyclic": [], "cyclic": [],
                         "fusion": False}
        return vcs[name]

    pending_acyclic: dict[str, list[str]] = {}

    for line in log_path.read_text(encoding="utf-8", errors="replace").splitlines():
        # Lake-level failure marker.
        lf = LAKE_FAIL_RE.match(line)
        if lf:
            module = lf.group(1)
            # e.g. AbstractRefinements.Test00.User.Proof.MaxProof
            if "Proof" in module:
                last = module.rsplit(".", 1)[-1]
                if last.endswith("Proof"):
                    _get(last[:-5])["failed"] = True
            continue

        # Lean info/error line referencing a Proof file.
        lm = LEAN_LINE_RE.match(line)
        if not lm:
            continue
        level_char = line.split(":", 1)[0]
        fpath, vc_name, message = lm.group(1), lm.group(2), lm.group(3)

        if level_char == "error":
            _get(vc_name)["failed"] = True
            continue

        if "[solve_fixpoint] Acyclic" in message:
            raw = re.search(r"\[([^\]]*)\]", message)
            pending_acyclic[vc_name] = _items(raw.group(1)) if raw else []
        elif "[solve_fixpoint] Cyclic" in message:
            raw = re.search(r"\[([^\]]*)\]", message)
            cyclic = _items(raw.group(1)) if raw else []
            acyclic = pending_acyclic.pop(vc_name, [])
            _get(vc_name)["acyclic"].extend(acyclic)
            _get(vc_name)["cyclic"].extend(cyclic)
        elif "fusion: eliminated" in message:
            _get(vc_name)["fusion"] = True

    for vc_name, acyclic in pending_acyclic.items():
        _get(vc_name)["acyclic"].extend(acyclic)

    return vcs


def run_merged(merged_dir: Path, log_path: Path) -> list[dict]:
    vc_info = parse_merged_log(log_path)

    vcs: list[dict] = []
    # VC files in merged project: <merged>/<Cat>/<Test>/Flux/VC/<Name>.lean
    for vc_path in sorted(merged_dir.rglob("Flux/VC/*.lean")):
        vc_name = vc_path.stem
        trivial = is_trivially_true(vc_path)

        # Derive a human-readable test_id from the path, e.g.:
        # .../AbstractRefinements/Test00/Flux/VC/Max.lean -> AbstractRefinements/Test00
        try:
            rel_parts = vc_path.relative_to(merged_dir).parts
            flux_idx = rel_parts.index("Flux")
            test_id = "/".join(rel_parts[:flux_idx])
        except (ValueError, IndexError):
            test_id = str(vc_path.parent.parent.parent)

        info = vc_info.get(vc_name, {})
        acyclic = info.get("acyclic", [])
        cyclic  = info.get("cyclic", [])
        # fusion eliminates acyclic κ before solve_fixpoint; treat as acyclic.
        if info.get("fusion") and not acyclic:
            acyclic = ["fusion"]

        vcs.append({
            "name":    f"{test_id}/{vc_name}",
            "trivial": trivial,
            "kappa":   classify(acyclic, cyclic),
            "failed":  info.get("failed", False),
        })
    return vcs


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Export per-VC lean-bench stats as JSON"
    )
    parser.add_argument(
        "bench_root", nargs="?", type=str,
        help="lean_bench root directory (per-test mode)",
    )
    parser.add_argument(
        "log_file", nargs="?", type=str,
        help="Log file path (per-test mode, default: lean_bench_log.txt)",
    )
    parser.add_argument(
        "--merged", type=str, metavar="DIR",
        help="Merged Lake project directory",
    )
    parser.add_argument(
        "--log", type=str, metavar="FILE",
        help="Log file (merged mode, default: lean_bench_log.txt)",
    )
    args = parser.parse_args()

    if args.merged:
        merged_dir = Path(args.merged).resolve()
        log_path = Path(args.log).resolve() if args.log else DEFAULT_LOG
        if not log_path.exists():
            print(f"error: log not found: {log_path}", file=sys.stderr)
            sys.exit(1)
        vcs = run_merged(merged_dir, log_path)
        log_dir = log_path.parent
    else:
        bench_root = Path(args.bench_root).resolve() if args.bench_root else DEFAULT_BENCH
        log_path   = Path(args.log_file).resolve() if args.log_file else DEFAULT_LOG
        if not log_path.exists():
            print(f"error: log not found: {log_path}", file=sys.stderr)
            sys.exit(1)
        if not bench_root.is_dir():
            print(f"error: lean_bench not found: {bench_root}", file=sys.stderr)
            sys.exit(1)
        vcs = run_pertest(bench_root, log_path)
        log_dir = log_path.parent

    suite: dict = {"suite": "Flux lean-bench", "vcs": vcs}
    suite.update(load_timing(log_dir))

    print(json.dumps([suite], indent=2))


if __name__ == "__main__":
    main()
