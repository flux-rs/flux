#!/usr/bin/env python3
"""Count and group Flux trusted functions.

Usage:
    tools/count_trusted.py [DIRECTORY ...]

Each reason is expected to begin with ``CATEGORY: message``.  Locations point
at the trusted attribute, so they can be opened directly by most shells/editors.
"""

# NOTE: Not human-written, rough edges or strange behaviors expected.  (not sure
# why this isn't just using `rg`; maybe it doesn't support multiline searches?)

import argparse
import os
import re
from collections import defaultdict
from pathlib import Path


YELLOW = "\033[33m"
RESET = "\033[0m"


ATTRIBUTE = re.compile(r"#\[\s*flux(?:_rs)?::trusted\b")
REASON = re.compile(r"\breason\s*=\s*\"")


def line_column(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    previous_newline = text.rfind("\n", 0, offset)
    return line, offset - previous_newline


def attribute_end(text: str, start: int) -> int | None:
    """Return the end of an attribute, respecting brackets and Rust strings."""
    depth = 0
    in_string = False
    escaped = False
    for index in range(start, len(text)):
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return index + 1
    return None


def rust_string(text: str, quote_start: int) -> tuple[str, int] | None:
    """Decode the basic escapes in a Rust string and return its end offset."""
    chars: list[str] = []
    index = quote_start + 1
    while index < len(text):
        char = text[index]
        if char == '"':
            return "".join(chars), index + 1
        if char == "\\" and index + 1 < len(text):
            escaped = text[index + 1]
            chars.append({"n": "\n", "r": "\r", "t": "\t"}.get(escaped, escaped))
            index += 2
        else:
            chars.append(char)
            index += 1
    return None


def is_after_comment_starter(text: str, offset: int) -> bool:
    """Heuristically detect comments before an attribute on the same line."""
    line_start = text.rfind("\n", 0, offset) + 1
    line_prefix = text[line_start:offset]
    return "//" in line_prefix or "/*" in line_prefix


def scan_file(path: Path) -> list[tuple[str, int, int, str]]:
    text = path.read_text(encoding="utf-8")
    results = []
    for match in ATTRIBUTE.finditer(text):
        # Hack for checking: this only looks for simple comment starters on
        # the same line; it is not intended to parse all Rust comment syntax.
        if is_after_comment_starter(text, match.start()):
            continue
        end = attribute_end(text, match.start())
        if end is None:
            continue
        reason_match = REASON.search(text, match.start(), end)
        reason = "(no reason)"
        if reason_match:
            parsed = rust_string(text, reason_match.end() - 1)
            if parsed is not None:
                reason = parsed[0].strip()

        if ":" in reason:
            category, message = reason.split(":", 1)
            category = category.strip() or "(uncategorized)"
            message = message.strip()
        else:
            category, message = "(uncategorized)", reason

        line, column = line_column(text, match.start())
        results.append((category, line, column, message))
    return results


def rust_files(directories: list[Path]):
    for directory in directories:
        if directory.is_file() and directory.suffix == ".rs":
            yield directory
            continue
        for root, dirnames, filenames in os.walk(directory):
            dirnames[:] = [name for name in dirnames if not name.startswith(".")]
            for filename in filenames:
                if filename.endswith(".rs"):
                    yield Path(root) / filename


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="*", type=Path, default=[Path(".")])
    args = parser.parse_args()

    grouped: dict[str, list[tuple[Path, int, int, str]]] = defaultdict(list)
    for path in rust_files(args.directories):
        for category, line, column, message in scan_file(path):
            grouped[category].append((path, line, column, message))

    for category in sorted(grouped):
        entries = grouped[category]
        print(f"{category}: ({len(entries)})")
        for path, line, column, message in sorted(entries):
            suffix = f" {message}" if message else ""
            print(f"{YELLOW}{path}{RESET}:{line}:{column}{suffix}")
        print()

    print(f"\nTotal: {sum(map(len, grouped.values()))}")


if __name__ == "__main__":
    main()
