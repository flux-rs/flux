#!/usr/bin/env python3
"""
Run lean builds and collect timing/kappa/error statistics.

Two modes:

  Per-test mode (original):
    python runlean.py <lean_bench_root>
    Finds every lean_proofs/ directory and runs lake build in each.

  Merged mode:
    python runlean.py --merged <merged_dir>
    Runs a single `lake build` in <merged_dir> (a project produced by
    merge_projects.sh) and parses the combined output.

In both modes the script writes lean_bench.time (total proof-check ms) to the
cwd and prints a log to stdout that export_lean_bench_stats.py can consume.
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


# ---------------------------------------------------------------------------
# Per-test mode (original behaviour)
# ---------------------------------------------------------------------------

def find_lean_proofs_dirs(root_path: Path) -> list[Path]:
    lean_dirs = []
    for dirpath, dirnames, _ in os.walk(root_path):
        if "lean_proofs" in dirnames:
            lean_dirs.append(Path(dirpath) / "lean_proofs")
    return lean_dirs


def run_lake_update(directory: Path) -> None:
    try:
        subprocess.run(["lake", "update"], cwd=directory,
                       capture_output=True, text=True, timeout=120)
    except Exception:
        pass


def run_lake_build_pertest(directory: Path):
    """Returns (success, error_output, kappa_lines, time_lines, proof_ms)."""
    try:
        result = subprocess.run(["lake", "build"], cwd=directory,
                                capture_output=True, text=True, timeout=300)
        all_lines = result.stdout.splitlines()
        error_lines  = [l for l in all_lines if l.startswith("error: ")]
        kappa_lines  = [l for l in all_lines if "[solve_fixpoint]" in l
                        or "fusion: eliminated" in l]
        time_lines   = [l for l in all_lines if "time: " in l
                        and l.strip().startswith("info:")]
        proof_ms = 0
        for tl in time_lines:
            try:
                proof_ms += int(tl.rsplit("time: ", 1)[1].removesuffix("ms"))
            except (ValueError, IndexError):
                pass
        has_error = result.returncode != 0 or len(error_lines) > 0
        return (not has_error, "\n".join(error_lines), kappa_lines,
                time_lines, proof_ms)
    except subprocess.TimeoutExpired:
        return (False, "Timeout expired (5 minutes)", [], [], 300_000)
    except FileNotFoundError:
        return (False, "lake command not found", [], [], 0)
    except Exception as e:
        return (False, str(e), [], [], 0)


def run_pertest(root_path: Path, verbose: bool) -> None:
    lean_dirs = find_lean_proofs_dirs(root_path)
    if not lean_dirs:
        print(f"No 'lean_proofs' directories found under '{root_path}'")
        sys.exit(0)

    print(f"Found {len(lean_dirs)} lean_proofs directories")
    print("-" * 60)

    visited = 0
    error_dirs: list[tuple[Path, str]] = []
    total_ms = 0

    for lean_dir in sorted(lean_dirs):
        visited += 1
        rel = lean_dir.relative_to(root_path)
        run_lake_update(lean_dir)
        print(f"[{visited}/{len(lean_dirs)}] Building: {rel} ... ",
              end="", flush=True)
        success, err_out, kappa_lines, time_lines, proof_ms = \
            run_lake_build_pertest(lean_dir)
        total_ms += proof_ms
        if success:
            print("OK")
        else:
            print("ERROR")
            error_dirs.append((lean_dir, err_out))
            if err_out:
                for e in err_out.splitlines():
                    print(f"    {e.strip()}")
        for kl in kappa_lines:
            print(f"    {kl.strip()}")
        for tl in time_lines:
            print(f"    {tl.strip()}")

    Path.cwd().joinpath("lean_bench.time").write_text(f"{total_ms}\n")
    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total directories visited: {visited}")
    print(f"Successful builds:         {visited - len(error_dirs)}")
    print(f"Failed builds:             {len(error_dirs)}")
    print(f"Total proof time:          {total_ms / 1000:.1f}s")
    if error_dirs:
        print("\nDirectories with errors:")
        for d, msg in error_dirs:
            print(f"  - {d.relative_to(root_path)}")
            if verbose and msg:
                print(f"      {msg.strip().split(chr(10))[0][:100]}")
    sys.exit(1 if error_dirs else 0)


# ---------------------------------------------------------------------------
# Merged mode
# ---------------------------------------------------------------------------

# Matches the Lake build-status line, e.g.:
#   ✔ [12/300] Building AbstractRefinements.Test00.Flux.VC.Max (42ms)
#   ✖ [13/300] Building AbstractRefinements.Test00.User.Proof.MaxProof (234ms)
LAKE_MODULE_RE = re.compile(
    r"^([✔✖])\s+\[\d+/\d+\]\s+Building\s+([\w.]+)"
)

# Lean info/error lines carry the source file path:
#   info: AbstractRefinements/Test00/User/Proof/MaxProof.lean:30:4: [solve_fixpoint] ...
#   error: AbstractRefinements/Test00/User/Proof/MaxProof.lean:30:4: ...
LEAN_LINE_RE = re.compile(
    r"^(info|error|warning):\s+(\S+\.lean):\d+:\d+:\s+(.*)"
)

# Extract VC name from a proof path component, e.g. "MaxProof.lean" -> "Max"
PROOF_FILE_RE = re.compile(r"(\w+)Proof\.lean$")


def _vc_name_from_proof_path(path_str: str) -> str | None:
    m = PROOF_FILE_RE.search(path_str)
    return m.group(1) if m else None


def run_lake_build_merged(merged_dir: Path):
    """Run lake build in merged_dir; return (returncode, wall_ms, stdout_lines)."""
    import time
    try:
        t0 = time.monotonic()
        result = subprocess.run(
            ["lake", "build"], cwd=merged_dir,
            capture_output=True, text=True, timeout=3600,
        )
        wall_ms = int((time.monotonic() - t0) * 1000)
        return result.returncode, wall_ms, result.stdout.splitlines()
    except subprocess.TimeoutExpired:
        return 1, 3_600_000, ["error: lake build timed out (1 hour)"]
    except FileNotFoundError:
        return 1, 0, ["error: lake command not found"]
    except Exception as e:
        return 1, 0, [f"error: {e}"]


def parse_merged_output(lines: list[str]) -> dict:
    """
    Parse raw `lake build` stdout from a merged project.

    Returns a dict keyed by vc_name with:
      {
        "failed": bool,
        "acyclic": list[str],
        "cyclic": list[str],
        "fusion_acyclic": bool,
        "time_ms": int,
        "kappa_lines": list[str],   # raw lines for the log
        "time_lines": list[str],
      }
    """
    vcs: dict[str, dict] = {}

    def _get(name: str) -> dict:
        if name not in vcs:
            vcs[name] = {
                "failed": False, "acyclic": [], "cyclic": [],
                "fusion_acyclic": False, "time_ms": 0,
                "kappa_lines": [], "time_lines": [],
            }
        return vcs[name]

    # Track modules that Lake reports as failed (✖).
    failed_modules: set[str] = set()

    # We need to pair Acyclic/Cyclic κ lines in document order per VC.
    # Keep a pending acyclic list per vc_name.
    pending_acyclic: dict[str, list[str]] = {}

    for line in lines:
        # Lake module status line.
        mlm = LAKE_MODULE_RE.match(line)
        if mlm:
            status, module = mlm.group(1), mlm.group(2)
            if status == "✖":
                failed_modules.add(module)
            continue

        # Lean info/error/warning line.
        lm = LEAN_LINE_RE.match(line)
        if not lm:
            continue
        level, fpath, message = lm.group(1), lm.group(2), lm.group(3)

        vc_name = _vc_name_from_proof_path(fpath)
        if vc_name is None:
            continue

        vc = _get(vc_name)

        if level == "error":
            vc["failed"] = True
            continue

        if level != "info":
            continue

        # [solve_fixpoint] Acyclic κ
        if "[solve_fixpoint] Acyclic" in message:
            raw = re.search(r"\[([^\]]*)\]", message)
            acyclic = _items(raw.group(1)) if raw else []
            pending_acyclic[vc_name] = acyclic
            vc["kappa_lines"].append(line)
            continue

        # [solve_fixpoint] Cyclic κ
        if "[solve_fixpoint] Cyclic" in message:
            raw = re.search(r"\[([^\]]*)\]", message)
            cyclic = _items(raw.group(1)) if raw else []
            acyclic = pending_acyclic.pop(vc_name, [])
            vc["acyclic"].extend(acyclic)
            vc["cyclic"].extend(cyclic)
            vc["kappa_lines"].append(line)
            continue

        # fusion: eliminated N acyclic κ
        if "fusion: eliminated" in message:
            vc["fusion_acyclic"] = True
            vc["kappa_lines"].append(line)
            continue

        # #time output
        if "time: " in message:
            tm = re.search(r"time:\s*(\d+)ms", message)
            if tm:
                vc["time_ms"] += int(tm.group(1))
                vc["time_lines"].append(line)

    # Flush any unmatched pending Acyclic lines (no Cyclic followed).
    for vc_name, acyclic in pending_acyclic.items():
        _get(vc_name)["acyclic"].extend(acyclic)

    # Apply Lake-level failures: if Lake reports ✖ for a proof module, mark failed.
    for module in failed_modules:
        # Module like AbstractRefinements.Test00.User.Proof.MaxProof
        vc_name = _vc_name_from_proof_path(module.replace(".", "/") + ".lean")
        if vc_name:
            _get(vc_name)["failed"] = True

    return vcs


def run_merged(merged_dir: Path, verbose: bool) -> None:
    print(f"Building merged project: {merged_dir}")
    print("-" * 60, flush=True)

    returncode, wall_ms, lines = run_lake_build_merged(merged_dir)

    # Print the raw lake output so it's captured in lean_bench_log.txt.
    for line in lines:
        print(line)

    vcs = parse_merged_output(lines)

    failed_vcs = [n for n, v in vcs.items() if v["failed"]]

    Path.cwd().joinpath("lean_bench.time").write_text(f"{wall_ms}\n")

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total VCs seen:   {len(vcs)}")
    print(f"Failed VCs:       {len(failed_vcs)}")
    print(f"lake build time:  {wall_ms / 1000:.1f}s")
    if failed_vcs and verbose:
        print("\nFailed VCs:")
        for n in sorted(failed_vcs):
            print(f"  - {n}")
    sys.exit(1 if (returncode != 0 or failed_vcs) else 0)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run lean builds for the lean_bench suite"
    )
    parser.add_argument(
        "path", nargs="?", type=str,
        help="Root path to search for lean_proofs directories (per-test mode)",
    )
    parser.add_argument(
        "--merged", type=str, metavar="DIR",
        help="Path to merged Lake project (run a single lake build)",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
    )
    args = parser.parse_args()

    if args.merged:
        merged_dir = Path(args.merged).resolve()
        if not merged_dir.is_dir():
            print(f"Error: '{merged_dir}' is not a directory", file=sys.stderr)
            sys.exit(1)
        run_merged(merged_dir, args.verbose)
    elif args.path:
        root_path = Path(args.path).resolve()
        if not root_path.exists():
            print(f"Error: '{root_path}' does not exist", file=sys.stderr)
            sys.exit(1)
        run_pertest(root_path, args.verbose)
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
