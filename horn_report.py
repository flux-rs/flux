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
import hashlib
import json
import re
import subprocess
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from pathlib import Path

# Result classes, in report order. `unsat` first: for a passing test it means something is wrong.
CLASSES = ["unsat", "error", "skipped", "sat", "unknown", "timeout", "crash"]

# Written by `-Fdump-smt-horn` for every query the formatter refused to encode.
SKIPPED_LOG = "_skipped.log"

LINE_COL = re.compile(r"line \d+ column \d+")

REASON = re.compile(r':reason-unknown\s+"(.*?)"', re.DOTALL)

COMMENT = re.compile(r"^\s*;")


@dataclass
class Result:
    file: str
    status: str
    seconds: float
    detail: str = ""
    # Other files carrying this same constraint, collapsed by --dedup.
    aliases: list[str] = field(default_factory=list)

    @property
    def normalized_detail(self) -> str:
        """Error text with line/column stripped, so the same bug groups across files."""
        return LINE_COL.sub("line L column C", self.detail)

    @property
    def message(self) -> str:
        """The error text alone, without the `(error "line N column M: ...")` wrapper."""
        text = self.detail.strip()
        if text.startswith('(error "'):
            text = text[len('(error "'):].removesuffix('")').removesuffix('"')
        return LINE_COL.sub("", text).lstrip(": ").strip()

    @property
    def summary(self) -> str:
        """One-line form of `detail` for the terminal; the full text stays in --json/--csv."""
        text = self.detail.split(" in <null>")[0].strip()
        head = text.split(" (")[0].strip().rstrip(":")
        if not head:
            head = text
        return head if len(head) <= 110 else head[:107] + "..."

    @property
    def label(self) -> str:
        return f"{self.file} (+{len(self.aliases)} dup)" if self.aliases else self.file


def constraint_key(path: Path) -> str:
    """Hash of a file's constraint, ignoring comments.

    Every dump carries a `;; Tag ... ESpan { span: <this test's source location> }` header, so two
    files holding the identical constraint are never byte-identical. Comparing the non-comment
    lines is what actually detects a repeated constraint.
    """
    body = "\n".join(
        line for line in path.read_text().splitlines() if not COMMENT.match(line)
    )
    return hashlib.md5(body.encode()).hexdigest()


def read_skipped(directory: Path) -> list[Result]:
    """Reads the queries the formatter declined to encode, from `_skipped.log`.

    These never became files, so they are invisible to the solver run -- but they are part of what
    the dump was asked to cover, and leaving them out silently overstates coverage.
    """
    log = directory / SKIPPED_LOG
    if not log.exists():
        return []
    seen, out = set(), []
    for line in log.read_text().splitlines():
        if not line.strip():
            continue
        # The log is appended to, so repeated dumps into one directory repeat entries.
        name, _, reason = line.partition("\t")
        if (name, reason) in seen:
            continue
        seen.add((name, reason))
        # A later run may have succeeded where an earlier one bailed out; trust the file.
        if (directory / f"{name}.smt2").exists():
            continue
        out.append(Result(f"{name}.smt2", "skipped", 0.0, reason or "no reason recorded"))
    return out


def dedup(files: list[Path]) -> tuple[list[Path], dict[str, list[str]]]:
    """Keeps the first file of each group of identical constraints.

    Returns the representatives and, for each, the names it stands in for.
    """
    groups: dict[str, list[Path]] = defaultdict(list)
    for path in files:
        groups[constraint_key(path)].append(path)
    keep, aliases = [], {}
    for group in groups.values():
        rep, *rest = sorted(group)
        keep.append(rep)
        aliases[rep.name] = [p.name for p in rest]
    return sorted(keep), aliases


def reason_unknown(path: Path, solver: str, timeout: int, extra: list[str]) -> str:
    """Asks the solver why it answered `unknown`.

    Worth the extra call: spacer's reason names the exact symbol it refused (`Uninterpreted 'c0'`,
    `Uninterpreted 'div'`), which distinguishes "outside the supported fragment" -- an encoding
    matter -- from "searched and gave up". The query is fed on stdin so the file is left alone.
    """
    text = path.read_text() + "\n(get-info :reason-unknown)\n"
    try:
        proc = subprocess.run(
            [solver, f"-T:{timeout}", *extra, "-in"],
            input=text, capture_output=True, text=True, timeout=timeout + 30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return ""
    m = REASON.search(proc.stdout + proc.stderr)
    if not m:
        return ""
    # Kept in full: for "formula is not in Horn fragment: <clause>" the text after the colon is
    # the offending clause, which is the whole point of asking. `Result.summary` trims it for
    # display; --json/--csv keep all of it.
    return " ".join(m.group(1).split())


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
    if first == "unknown":
        return Result(path.name, first, elapsed, reason_unknown(path, solver, timeout, extra))
    if first in ("sat", "unsat", "timeout"):
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

    print(f"\n{title} ({total} queries){note}")
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


def report(
    results: list[Result], timeout: int, elapsed: float, top: int, deduped: bool = False
) -> None:
    total = len(results)
    by_class: dict[str, list[Result]] = {c: [] for c in CLASSES}
    for r in results:
        by_class.setdefault(r.status, []).append(r)

    collapsed = sum(len(r.aliases) for r in results)
    n_skipped = sum(1 for r in results if r.status == "skipped")
    scope = f"{total - n_skipped} constraint files"
    if collapsed:
        scope = f"{total - n_skipped} distinct constraints ({collapsed} duplicates collapsed)"
    if n_skipped:
        scope += f" + {n_skipped} not encoded"
    print(f"\n{scope}, {elapsed:.1f}s wall clock, {timeout}s per-file timeout")

    malformed = by_class.get("error") or []
    if malformed:
        groups: dict[str, list[Result]] = {}
        for r in malformed:
            groups.setdefault(r.normalized_detail, []).append(r)
        print(f"\nmalformed files ({len(malformed)} files, {len(groups)} distinct errors)")
        print("-" * 58)
        width = max(len(r.label) for r in malformed)
        for r in sorted(malformed, key=lambda r: (r.normalized_detail, r.file)):
            print(f"  {r.label:<{width}}  {r.message}")
        if len(groups) > 1:
            print("\n  distinct errors:")
            for detail, items in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                print(f"    [{len(items)}] {items[0].message}")

    skipped = by_class.get("skipped") or []
    if skipped:
        by_reason: dict[str, list[Result]] = {}
        for r in skipped:
            by_reason.setdefault(r.detail, []).append(r)
        note = " -- no file, so --dedup cannot collapse these" if deduped else ""
        print(
            f"\nnot encoded, skipped by the formatter "
            f"({len(skipped)} queries, {len(by_reason)} distinct{note})"
        )
        print("-" * 58)
        width = max(len(r.file) - 5 for r in skipped)
        for r in sorted(skipped, key=lambda r: (r.detail, r.file)):
            print(f"  {r.file[:-5]:<{width}}  {r.detail}")

    for cls in ("unsat", "crash"):
        items = by_class.get(cls) or []
        if items:
            print(f"\n{cls} files ({len(items)})")
            print("-" * 58)
            for r in sorted(items, key=lambda r: r.file):
                suffix = f"  {r.detail}" if r.detail else ""
                print(f"  {r.label}{suffix}")

    hard = sorted(
        (by_class.get("timeout") or []) + (by_class.get("unknown") or []),
        key=lambda r: r.file,
    )
    if hard:
        print(f"\nnot solved ({len(hard)})")
        print("-" * 58)
        width = max(len(r.label) for r in hard)
        for r in hard:
            reason = f"  {r.summary}" if r.detail else ""
            print(f"  {r.status:<8} {r.label:<{width}}{reason}".rstrip())

    solved = sorted(
        (by_class.get("sat") or []) + (by_class.get("unsat") or []),
        key=lambda r: -r.seconds,
    )
    if solved and top:
        print(f"\nslowest solved (top {min(top, len(solved))} of {len(solved)})")
        print("-" * 58)
        for r in solved[:top]:
            print(f"  {r.seconds:>7.2f}s  {r.status:<5} {r.label}")
        times = [r.seconds for r in solved]
        times.sort()
        median = times[len(times) // 2]
        print(f"\n  median {median:.2f}s   total {sum(times):.1f}s over {len(times)} solved")

    # Stats last, so they are on screen at the end of a long run. Two universes: every query the
    # dump covered, and only those the solver actually got to work on. The second is the one that
    # says how spacer does -- a malformed or skipped query measures the formatter, not the solver,
    # so leaving those in drags every percentage down for an unrelated reason.
    print()
    print("=" * 58)
    print("STATS")
    print("=" * 58)
    distribution("all queries", results)
    reached = [r for r in results if r.status not in ("error", "skipped")]
    excluded = []
    if malformed:
        excluded.append(f"{len(malformed)} malformed")
    if skipped:
        excluded.append(f"{len(skipped)} not encoded")
    note = f", excluding {' and '.join(excluded)}" if excluded else ", nothing excluded"
    distribution("reached the solver", reached, note)

    if reached:
        n = sum(1 for r in reached if r.status in ("sat", "unsat"))
        print(
            f"\n  solved {n}/{len(reached)} of those reaching the solver "
            f"({100 * n / len(reached):.1f}%)"
            f"   |   {n}/{total} of all queries ({100 * n / total:.1f}%)"
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
    p.add_argument(
        "--dedup",
        action="store_true",
        help="solve each distinct constraint once. Files are compared ignoring comments, since "
        "the per-test span header makes otherwise identical dumps byte-distinct",
    )
    p.add_argument("--top", type=int, default=10, help="how many slowest files to list (0 to skip)")
    p.add_argument("-q", "--quiet", action="store_true", help="no per-file progress")
    args = p.parse_args()

    if not args.dir.is_dir():
        sys.exit(f"not a directory: {args.dir}")
    files = sorted(f for f in args.dir.glob("*.smt2") if not args.only or args.only in f.name)
    # Read before the guard below: a directory can legitimately hold only skipped queries.
    skipped = [r for r in read_skipped(args.dir) if not args.only or args.only in r.file]
    if not files and not skipped:
        sys.exit(f"no matching .smt2 files in {args.dir}")

    aliases: dict[str, list[str]] = {}
    if args.dedup:
        before = len(files)
        files, aliases = dedup(files)
        print(f"dedup: {before} files -> {len(files)} distinct constraints")

    jobs = args.jobs or None
    results: list[Result] = []
    start = time.monotonic()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = [
            pool.submit(run_one, f, args.solver, args.timeout, args.solver_arg) for f in files
        ]
        for i, fut in enumerate(futures, 1):
            r = fut.result()
            r.aliases = aliases.get(r.file, [])
            results.append(r)
            if not args.quiet:
                print(f"[{i:>4}/{len(files)}] {r.status:<8} {r.seconds:>6.2f}s  {r.label}")

    elapsed = time.monotonic() - start
    report(results + skipped, args.timeout, elapsed, args.top, args.dedup)

    rows = [asdict(r) for r in sorted(results + skipped, key=lambda r: r.file)]
    for row in rows:
        row["duplicates"] = len(row["aliases"])
    if args.json:
        args.json.write_text(json.dumps(rows, indent=2))
        print(f"\nwrote {args.json}")
    if args.csv:
        with args.csv.open("w", newline="") as fh:
            fields = ["file", "status", "seconds", "duplicates", "detail"]
            w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
            w.writeheader()
            w.writerows(rows)
        print(f"wrote {args.csv}")

    # Non-zero if anything is actually broken; timeouts and unknown are not failures.
    # A skipped query is a known limitation, not a failure, so it does not affect the exit code.
    bad = sum(1 for r in results if r.status in ("unsat", "error", "crash"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
