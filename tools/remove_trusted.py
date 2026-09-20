#!/usr/bin/env python3
"""Remove trusted attributes whose reason starts with a chosen identifier.

Usage:
    tools/remove_trusted.py [--write] [--identifier ID] [DIRECTORY ...]

Without ``--write`` this is a preview and only reports matching attributes.
The default identifier is ``ICE``.  A reason such as ``ICE: workaround`` is
considered a match.
"""

import argparse
import os
import re
from pathlib import Path


# Match #[trusted], #[flux::trusted], and similar attribute paths.
ATTRIBUTE = re.compile(r"#\[\s*(?:(?:[A-Za-z_]\w*)\s*::\s*)*(trusted|trusted_impl)\b")
REASON = re.compile(r"\breason\s*=\s*\"")


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
                # HACK: remove newlines at end; not general
                if index <= len(text) and text[index + 1] == "\n":
                    return index + 2
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
    """Avoid treating an attribute-looking string in a line comment as code."""
    line_start = text.rfind("\n", 0, offset) + 1
    line_prefix = text[line_start:offset]
    return "//" in line_prefix or "/*" in line_prefix


def matching_attributes(text: str, identifier: str) -> list[tuple[int, int]]:
    matches = []
    for match in ATTRIBUTE.finditer(text):
        if is_after_comment_starter(text, match.start()):
            continue
        end = attribute_end(text, match.start())
        if end is None:
            continue
        reason_match = REASON.search(text, match.start(), end)
        if reason_match is None:
            continue
        parsed = rust_string(text, reason_match.end() - 1)
        if parsed is None:
            continue
        reason_identifier = parsed[0].split(":", 1)[0].strip()
        if reason_identifier == identifier:
            matches.append((match.start(), end))
    return matches


def line_column(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    previous_newline = text.rfind("\n", 0, offset)
    return line, offset - previous_newline


def removal_end(text: str, start: int, end: int) -> tuple[int, int]:
    """Include surrounding whitespace when the attribute occupies its own line."""
    line_start = text.rfind("\n", 0, start) + 1
    if text[line_start:start].strip():
        return start, end

    if end > start and text[end - 1] == "\n":
        return line_start, end

    line_end = text.find("\n", end)
    if line_end == -1 or text[end:line_end].strip():
        return start, end
    return line_start, line_end + 1


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
    parser.add_argument(
        "--identifier",
        default="ICE",
        help="reason identifier to remove (default: ICE)",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write changes; without this flag, only show what would change",
    )
    parser.add_argument("directories", nargs="*", type=Path, default=[Path(".")])
    args = parser.parse_args()

    changed_files = 0
    removed_attributes = 0
    for path in rust_files(args.directories):
        text = path.read_text(encoding="utf-8")
        matches = [
            removal_end(text, start, end)
            for start, end in matching_attributes(text, args.identifier)
        ]
        if not matches:
            continue

        changed_files += 1
        removed_attributes += len(matches)
        for start, _ in matches:
            line, column = line_column(text, start)
            print(f"{path}:{line}:{column}")

        if args.write:
            for start, end in reversed(matches):
                text = text[:start] + text[end:]
            path.write_text(text, encoding="utf-8")

    action = "Removed" if args.write else "Would remove"
    print(f"{action} {removed_attributes} attribute(s) in {changed_files} file(s).")


if __name__ == "__main__":
    main()
