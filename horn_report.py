#!/usr/bin/env python3
"""Run a CHC solver over a directory of SMT-LIB HORN files and report the results.

Produces the files dumped by `-Fdump-smt-horn=DIR`:

    FLUX_POS_ONLY=1 FLUXFLAGS="-Fdump-smt-horn=/tmp/horn" cargo xtask test --suite basic
    ./horn_report.py /tmp/horn

Each file is expected to be `sat` (the constraint is satisfiable, i.e. an assignment to the
kvars exists), since these come from tests that verify. `unsat` therefore means either a real
encoding bug or a test that is not supposed to verify, and is reported first.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass
from pathlib import Path

# Result classes, in report order. `unsat` first: for a passing test it means something is wrong.
CLASSES = ["unsat", "error", "sat", "unknown", "timeout", "crash"]

LINE_COL = re.compile(r"line \d+ column \d+")


@dataclass
class Result:
    file: str
    status: str
    seconds: float
    detail: str = ""

    @property
    def normalized_detail(self) -> str:
        """Error text with line/column stripped, so the same bug groups across files."""
        return LINE_COL.sub("line L column C", self.detail)


def run_one(path: Path, solver: str, timeout: int, extra: list[str]) -> Result:
    cmd = [solver, f"-T:{timeout}", *extra, str(path)]
    start = time.monotonic()
    try:
        # The wall-clock guard is deliberately looser than -T: z3's soft timeout does not cover
        # parsing, and a hung process would otherwise stall the pool.
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout + 30
        )
        out = (proc.stdout + proc.stderr).strip()
    except subprocess.TimeoutExpired:
        return Result(path.name, "timeout", time.monotonic() - start, "killed by wall clock")
    except FileNotFoundError:
        sys.exit(f"solver not found: {solver}")
    elapsed = time.monotonic() - start

    lines = [line for line in out.splitlines() if line.strip()]
    first = lines[0] if lines else ""

    # An `(error ...)` anywhere means the file was not fully understood, even when a later line
    # says `sat` -- z3 keeps going after a bad command, so the verdict is meaningless.
    errors = [line for line in lines if line.startswith('(error')]
    if errors:
        return Result(path.name, "error", elapsed, errors[0])
    if first in ("sat", "unsat", "unknown", "timeout"):
        return Result(path.name, first, elapsed)
    return Result(path.name, "crash", elapsed, first or f"no output (exit {proc.returncode})")


def bar(count: int, total: int, width: int = 28) -> str:
    filled = 0 if not total else round(width * count / total)
    return "#" * filled + "." * (width - filled)


def distribution(title: str, results: list[Result], note: str = "") -> None:
    """Prints the status distribution over `results`, which is the universe percentages use."""
    total = len(results)
    counts: dict[str, int] = {}
    for r in results:
        counts[r.status] = counts.get(r.status, 0) + 1

    print(f"\n{title} ({total} files){note}")
    print("-" * 58)
    if not total:
        print("  nothing to report")
        return
    print(f"  {'status':<9} {'count':>5}  {'%':>6}  distribution")
    for cls in CLASSES:
        count = counts.get(cls, 0)
        if not count:
            continue
        pct = 100 * count / total
        print(f"  {cls:<9} {count:>5}  {pct:>5.1f}%  {bar(count, total)}")


def report(results: list[Result], timeout: int, elapsed: float, top: int) -> None:
    total = len(results)
    by_class: dict[str, list[Result]] = {c: [] for c in CLASSES}
    for r in results:
        by_class.setdefault(r.status, []).append(r)

    print(f"\n{total} files, {elapsed:.1f}s wall clock, {timeout}s per-file timeout")

    malformed = by_class.get("error") or []
    if malformed:
        groups: dict[str, list[Result]] = {}
        for r in malformed:
            groups.setdefault(r.normalized_detail, []).append(r)
        print(f"\nmalformed files, grouped by error ({len(malformed)} files, {len(groups)} distinct)")
        print("-" * 58)
        for detail, items in sorted(groups.items(), key=lambda kv: -len(kv[1])):
            print(f"  [{len(items)}] {detail}")
            for r in sorted(items, key=lambda r: r.file):
                print(f"        {r.file}")

    for cls in ("unsat", "crash"):
        items = by_class.get(cls) or []
        if items:
            print(f"\n{cls} files ({len(items)})")
            print("-" * 58)
            for r in sorted(items, key=lambda r: r.file):
                suffix = f"  {r.detail}" if r.detail else ""
                print(f"  {r.file}{suffix}")

    hard = sorted(
        (by_class.get("timeout") or []) + (by_class.get("unknown") or []),
        key=lambda r: r.file,
    )
    if hard:
        print(f"\nnot solved ({len(hard)})")
        print("-" * 58)
        for r in hard:
            print(f"  {r.status:<8} {r.file}")

    solved = sorted(
        (by_class.get("sat") or []) + (by_class.get("unsat") or []),
        key=lambda r: -r.seconds,
    )
    if solved and top:
        print(f"\nslowest solved (top {min(top, len(solved))} of {len(solved)})")
        print("-" * 58)
        for r in solved[:top]:
            print(f"  {r.seconds:>7.2f}s  {r.status:<5} {r.file}")
        times = [r.seconds for r in solved]
        times.sort()
        median = times[len(times) // 2]
        print(f"\n  median {median:.2f}s   total {sum(times):.1f}s over {len(times)} solved")

    # Stats last, so they are on screen at the end of a long run. Two universes: everything that
    # was dumped, and only the files the solver actually understood. The second is the one that
    # says how the solver does on the constraints -- a malformed file measures the formatter, not
    # spacer, so leaving it in drags every percentage down for an unrelated reason.
    print()
    print("=" * 58)
    print("STATS")
    print("=" * 58)
    distribution("all files", results)
    well_formed = [r for r in results if r.status != "error"]
    note = f", excluding {len(malformed)} malformed" if malformed else ", none malformed"
    distribution("well-formed only", well_formed, note)

    if well_formed:
        solved_wf = sum(1 for r in well_formed if r.status in ("sat", "unsat"))
        print(
            f"\n  solved {solved_wf}/{len(well_formed)} well-formed "
            f"({100 * solved_wf / len(well_formed):.1f}%)"
            f"   |   {solved_wf}/{total} of all dumped "
            f"({100 * solved_wf / total:.1f}%)"
        )


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("dir", type=Path, help="directory of .smt2 files")
    p.add_argument("-T", "--timeout", type=int, default=15, help="per-file timeout in seconds (default 15)")
    p.add_argument("-j", "--jobs", type=int, default=0, help="parallel solver processes (default: cpu count)")
    p.add_argument("--solver", default="z3", help="solver binary (default z3)")
    p.add_argument("--solver-arg", action="append", default=[], help="extra solver argument, repeatable")
    p.add_argument("--json", type=Path, help="also write per-file results as JSON")
    p.add_argument("--csv", type=Path, help="also write per-file results as CSV")
    p.add_argument("--only", help="only files whose name contains this substring")
    p.add_argument("--top", type=int, default=10, help="how many slowest files to list (0 to skip)")
    p.add_argument("-q", "--quiet", action="store_true", help="no per-file progress")
    args = p.parse_args()

    if not args.dir.is_dir():
        sys.exit(f"not a directory: {args.dir}")
    files = sorted(f for f in args.dir.glob("*.smt2") if not args.only or args.only in f.name)
    if not files:
        sys.exit(f"no matching .smt2 files in {args.dir}")

    jobs = args.jobs or None
    results: list[Result] = []
    start = time.monotonic()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = [
            pool.submit(run_one, f, args.solver, args.timeout, args.solver_arg) for f in files
        ]
        for i, fut in enumerate(futures, 1):
            r = fut.result()
            results.append(r)
            if not args.quiet:
                print(f"[{i:>4}/{len(files)}] {r.status:<8} {r.seconds:>6.2f}s  {r.file}")

    elapsed = time.monotonic() - start
    report(results, args.timeout, elapsed, args.top)

    rows = [asdict(r) for r in sorted(results, key=lambda r: r.file)]
    if args.json:
        args.json.write_text(json.dumps(rows, indent=2))
        print(f"\nwrote {args.json}")
    if args.csv:
        with args.csv.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["file", "status", "seconds", "detail"])
            w.writeheader()
            w.writerows(rows)
        print(f"wrote {args.csv}")

    # Non-zero if anything is actually broken; timeouts and unknown are not failures.
    bad = sum(1 for r in results if r.status in ("unsat", "error", "crash"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
