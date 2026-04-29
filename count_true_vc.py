#!/usr/bin/env python3
from pathlib import Path
import re

root = Path(__file__).resolve().parent
bench_dir = root / "tests" / "lean_bench"

count = 0
matches = []
for path in sorted(bench_dir.rglob("*.lean")):
    if "/VC/" not in path.as_posix():
        continue

    try:
        text = path.read_text(encoding="utf-8", errors="strict")
    except (UnicodeDecodeError, OSError):
        continue

    lines = text.splitlines()
    def_indices = [i for i, line in enumerate(lines) if re.match(r"^\s*def\b", line)]
    if not def_indices:
        continue

    last_def_idx = def_indices[-1]
    last_def_line = lines[last_def_idx]
    rhs_match = re.search(r":=\s*(.*)$", last_def_line)

    if rhs_match and rhs_match.group(1).strip():
        body = rhs_match.group(1).strip()
    else:
        def_indent = len(last_def_line) - len(last_def_line.lstrip(" "))
        body_lines = []
        for line in lines[last_def_idx + 1 :]:
            if not line.strip():
                body_lines.append(line)
                continue
            indent = len(line) - len(line.lstrip(" "))
            if indent <= def_indent:
                break
            body_lines.append(line)
        body = "\n".join(body_lines).strip()

    if body == "True":
        count += 1
        matches.append(path.relative_to(root))

print(count)
for match in matches:
    print(match)
