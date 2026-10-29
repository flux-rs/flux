#!/usr/bin/env python3
"""
Migrates a project from the old Flux configuration format to the current one, introduced in
https://github.com/flux-rs/flux/pull/1883.

In the old format, `[package.metadata.flux]` in `Cargo.toml` used snake_case keys and also held
settings like `cache`, and a `flux.toml` file overrode the manifest of every package. In the
current format:

* `[package.metadata.flux]` only holds properties of the crate, with kebab-case keys. Defaults for
  trusted and ignored items move to the `trusted`, `trusted-impl` and `ignore` subtables.
* Settings (`cache`, `dump_constraint`) move to `.flux/config.toml`.
* Crate properties set in `flux.toml` become `build.fluxflags`, which also come after the flags
  derived from the manifest. A `[dev]` table in `flux.toml` is left there because the driver reads
  it from that file.

Manifests are edited in place, keeping comments and formatting. Every file found under each PATH
is migrated, and settings from manifests are written to `PATH/.flux/config.toml`.

Usage:
    python migrate_flux_config.py [--dry-run] PATH...
"""

import argparse
import difflib
import json
import re
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

# Keys of `[package.metadata.flux]` that are unchanged.
UNCHANGED = {"enabled", "include", "solver", "lean"}

# Keys of `[package.metadata.flux]` that are renamed.
RENAMED = {
    "check_overflow": "check-overflow",
    "no_panic": "no-panic",
    "allow_uninterpreted_cast": "allow-uninterpreted-cast",
    "scrape_quals": "scrape-quals",
    "uif_ops": "uif-ops",
}

# Keys of `[package.metadata.flux]` that move to a subtable, as `(table, key)`.
MOVED = {
    "default_trusted": ("trusted", "default"),
    "include_trusted": ("trusted", "files"),
    "include_trusted_impl": ("trusted-impl", "files"),
    "default_ignore": ("ignore", "default"),
}

# Keys that move to `.flux/config.toml`, as `(table, key)`.
SETTINGS = {
    "cache": ("cache", "enabled"),
    "dump_constraint": ("debug", "dump-constraint"),
}

# Keys of the current format, left as they are if a manifest is partially migrated.
CURRENT = UNCHANGED | set(RENAMED.values()) | {"allow-raw-deref", "trusted", "trusted-impl", "ignore"}

# Flags for the crate properties that can be set in `flux.toml`.
FLAGS = {
    "solver": "solver",
    "check_overflow": "check-overflow",
    "uif_ops": "uif-ops",
    "lean": "lean",
    "scrape_quals": "scrape-quals",
    "default_trusted": "trusted",
    "default_ignore": "ignore",
    "no_panic": "no-panic",
    "allow_uninterpreted_cast": "allow-uninterpreted-cast",
    "include": "include",
    "include_trusted": "include-trusted",
    "include_trusted_impl": "include-trusted-impl",
}

# Older versions of Flux took a boolean for `check_overflow`.
OVERFLOW_MODES = {True: "strict", False: "none"}

FLUX_TABLE = "package.metadata.flux"

SKIPPED_DIRS = {".git", "target", "node_modules"}

KEY_RE = re.compile(r"^(\s*)(#\s*)?([A-Za-z0-9_-]+)(\s*=)(.*)$")


class MigrationError(Exception):
    pass


@dataclass
class Item:
    """A key with its value, a commented-out key, or any other line in the body of a table."""

    key: str | None
    commented: bool
    lines: list[str]


@dataclass
class Package:
    name: str
    enabled: bool
    settings: dict[tuple[str, str], Any]


@dataclass
class Config:
    """The content of a `.flux/config.toml`."""

    fluxflags: list[str] = field(default_factory=list)
    settings: dict[tuple[str, str], Any] = field(default_factory=dict)
    overrides: dict[str, dict[tuple[str, str], Any]] = field(default_factory=dict)

    def is_empty(self) -> bool:
        return not (self.fluxflags or self.settings or self.overrides)


@dataclass
class Plan:
    """The changes to make, computed before writing anything."""

    writes: dict[Path, str] = field(default_factory=dict)
    deletes: list[Path] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


def bracket_depth(text: str, depth: int) -> int:
    """Returns the nesting depth of brackets and braces after `text`, ignoring strings and comments."""
    quote = None
    i = 0
    while i < len(text):
        c = text[i]
        if quote:
            if c == "\\" and quote == '"':
                i += 1
            elif c == quote:
                quote = None
        elif c in "\"'":
            quote = c
        elif c == "#":
            break
        elif c in "[{":
            depth += 1
        elif c in "]}":
            depth -= 1
        i += 1
    return depth


def header_name(line: str) -> str:
    """The name of a table header, e.g., `package.metadata.flux` for `[package . metadata."flux"]`."""
    inner = line.strip().split("#", 1)[0].strip()
    return re.sub(r"[\s\"']", "", inner)


def split_sections(lines: list[str]) -> list[tuple[str | None, list[str]]]:
    """Splits a document into the lines before the first table and one section per table, each
    starting with its header."""
    sections: list[tuple[str | None, list[str]]] = [(None, [])]
    depth = 0
    for line in lines:
        if depth == 0 and line.lstrip().startswith("["):
            sections.append((header_name(line), [line]))
        else:
            sections[-1][1].append(line)
        depth = bracket_depth(line, depth)
    return sections


def split_items(lines: list[str]) -> list[Item]:
    items: list[Item] = []
    depth = 0
    for line in lines:
        if depth > 0:
            items[-1].lines.append(line)
            depth = bracket_depth(line, depth)
            continue
        m = KEY_RE.match(line.rstrip("\r\n"))
        if m and not m.group(2):
            items.append(Item(m.group(3), False, [line]))
            depth = bracket_depth(m.group(5), 0)
        elif m:
            items.append(Item(m.group(3), True, [line]))
        else:
            items.append(Item(None, False, [line]))
    return items


def rename_key(line: str, new_key: str) -> str:
    body = line.rstrip("\r\n")
    m = KEY_RE.match(body)
    assert m
    return m.group(1) + (m.group(2) or "") + new_key + m.group(4) + m.group(5) + line[len(body) :]


def replace_bool(line: str, value: Any) -> str:
    """Replaces a boolean value in `line` by `value` if it is a string."""
    if not isinstance(value, str):
        return line
    return re.sub(r"=(\s*)(true|false)\b", lambda m: f"={m.group(1)}{json.dumps(value)}", line, count=1)


def without_indent(lines: list[str]) -> list[str]:
    return [lines[0].lstrip(), *lines[1:]]


def migrate_value(key: str, value: Any) -> Any:
    if key == "check_overflow" and isinstance(value, bool):
        return OVERFLOW_MODES[value]
    return value


def migrate_flux_table(old: dict[str, Any]) -> tuple[dict[str, Any], dict[tuple[str, str], Any]]:
    """Returns the migrated `[package.metadata.flux]` table and the settings taken out of it."""
    new: dict[str, Any] = {}
    settings = {}
    for key, value in old.items():
        if key in SETTINGS:
            settings[SETTINGS[key]] = value
        elif key in MOVED:
            table, new_key = MOVED[key]
            new.setdefault(table, {})[new_key] = value
        elif key in RENAMED:
            new[RENAMED[key]] = migrate_value(key, value)
        elif key in CURRENT:
            if isinstance(value, dict):
                new.setdefault(key, {}).update(value)
            else:
                new[key] = value
        else:
            raise MigrationError(f"unknown key `{key}` in `[{FLUX_TABLE}]`")
    return new, settings


def migrate_manifest(path: Path, plan: Plan) -> Package | None:
    """Migrates `[package.metadata.flux]` in the manifest at `path`. Returns `None` if the manifest
    doesn't have the table."""
    text = path.read_text()
    data = tomllib.loads(text)
    old = data.get("package", {}).get("metadata", {}).get("flux")
    if not isinstance(old, dict):
        return None
    new, settings = migrate_flux_table(old)
    package = Package(data["package"].get("name", path.parent.name), bool(old.get("enabled")), settings)

    sections = split_sections(text.splitlines(keepends=True))
    flux_sections = [i for i, (name, _) in enumerate(sections) if name == f"[{FLUX_TABLE}]"]
    if len(flux_sections) != 1:
        if new != old:
            raise MigrationError(
                f"`[{FLUX_TABLE}]` is not written as a table header; migrate it by hand"
            )
        return package
    index = flux_sections[0]
    header, *body = sections[index][1]

    kept: list[str] = []
    moved: dict[str, list[str]] = {}
    for item in split_items(body):
        if item.key is None:
            kept.extend(item.lines)
        elif item.key in RENAMED:
            line = rename_key(item.lines[0], RENAMED[item.key])
            if not item.commented:
                line = replace_bool(line, migrate_value(item.key, old[item.key]))
            kept.extend([line, *item.lines[1:]])
        elif item.commented:
            if item.key in MOVED or item.key in SETTINGS:
                plan.warnings.append(f"{path}: left commented-out `{item.key}` unchanged")
            kept.extend(item.lines)
        elif item.key in MOVED:
            table, new_key = MOVED[item.key]
            lines = without_indent(item.lines)
            moved.setdefault(table, []).extend([rename_key(lines[0], new_key), *lines[1:]])
        elif item.key in SETTINGS:
            pass
        else:
            kept.extend(item.lines)

    # Add the subtables after the last line of the table that isn't blank
    end = len(kept)
    while end > 0 and not kept[end - 1].strip():
        end -= 1
    tables = []
    for table, lines in moved.items():
        tables.extend(["\n", f"[{FLUX_TABLE}.{table}]\n", *lines])
    if tables and end > 0 and not kept[end - 1].endswith("\n"):
        kept[end - 1] += "\n"
    kept[end:end] = tables

    sections[index] = (sections[index][0], [header, *kept])
    new_text = "".join(line for _, lines in sections for line in lines)
    if new_text == text:
        return package

    # Check that only `[package.metadata.flux]` changed, and that it changed as expected
    try:
        new_data = tomllib.loads(new_text)
    except tomllib.TOMLDecodeError as err:
        raise MigrationError(f"migrated manifest is not valid TOML ({err}); migrate it by hand")
    if new_data["package"]["metadata"].pop("flux") != new:
        raise MigrationError(f"failed to migrate `[{FLUX_TABLE}]`; migrate it by hand")
    data["package"]["metadata"].pop("flux")
    if new_data != data:
        raise MigrationError("migrating changed more than `[package.metadata.flux]`")
    plan.writes[path] = new_text
    return package


def to_flags(key: str, value: Any) -> list[str]:
    value = migrate_value(key, value)
    values = value if isinstance(value, list) else [value]
    return [f"-F{FLAGS[key]}={json.dumps(v) if isinstance(v, bool) else v}" for v in values]


def migrate_flux_toml(path: Path, plan: Plan) -> Config:
    """Removes the keys of `flux.toml` that `cargo flux` used to read and returns them as the
    content of a `.flux/config.toml`, with crate properties as `build.fluxflags`."""
    text = path.read_text()
    data = tomllib.loads(text)
    flags = []
    settings = {}
    for key, value in data.items():
        if isinstance(value, dict):
            continue
        if key in SETTINGS:
            settings[SETTINGS[key]] = value
        elif key in FLAGS:
            if key.startswith("include"):
                plan.warnings.append(
                    f"{path}: `{key}` used to replace the patterns of each manifest and be relative "
                    f"to each package, but `-F{FLAGS[key]}` flags add to the patterns of the "
                    f"manifest. Check that the result is what you want."
                )
            flags.extend(to_flags(key, value))
        else:
            raise MigrationError(f"unknown key `{key}` in `{path}`")

    preamble, *tables = split_sections(text.splitlines(keepends=True))
    kept = [line for item in split_items(preamble[1]) if item.key is None or item.commented for line in item.lines]
    new_text = "".join(kept + [line for _, lines in tables for line in lines])
    if not any(line.strip() and not line.lstrip().startswith("#") for line in new_text.splitlines()):
        plan.deletes.append(path)
    elif new_text != text:
        plan.writes[path] = new_text.lstrip("\n")
    return Config(flags, settings)


def toml_value(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ", ".join(toml_value(v) for v in value) + "]"
    return str(value)


def render_config(config: Config) -> str:
    sections = []
    if config.fluxflags:
        sections.append(f"[build]\nfluxflags = {toml_value(config.fluxflags)}\n")
    settings = sorted(config.settings.items())
    for table in sorted({table for table, _ in config.settings}):
        lines = [f"{key} = {toml_value(v)}\n" for (t, key), v in settings if t == table]
        sections.append(f"[{table}]\n" + "".join(lines))
    for name, package_settings in sorted(config.overrides.items()):
        lines = [f"{t}.{key} = {toml_value(v)}\n" for (t, key), v in sorted(package_settings.items())]
        spec = name if re.fullmatch(r"[A-Za-z0-9_-]+", name) else json.dumps(name)
        sections.append(f"[package.{spec}]\n" + "".join(lines))
    return "\n".join(sections)


def add_package_settings(config: Config, packages: list[Package]) -> None:
    """Adds the settings of `packages` to `config`, at the top level if every package checked by
    Flux has the same value and as package overrides otherwise. Settings already in `config` came
    from `flux.toml`, which overrode every package."""
    enabled = [package for package in packages if package.enabled]
    for key in sorted({key for package in enabled for key in package.settings}):
        if key in config.settings:
            continue
        values = [package.settings.get(key) for package in enabled]
        if values[0] is not None and all(value == values[0] for value in values):
            config.settings[key] = values[0]
        else:
            for package in enabled:
                if key in package.settings:
                    config.overrides.setdefault(package.name, {})[key] = package.settings[key]


def find_files(root: Path, name: str) -> list[Path]:
    found = []
    for path in sorted(root.rglob(name)):
        if not SKIPPED_DIRS.intersection(path.relative_to(root).parts):
            found.append(path)
    return found


def plan_migration(root: Path, plan: Plan) -> None:
    packages = []
    for manifest in find_files(root, "Cargo.toml"):
        try:
            package = migrate_manifest(manifest, plan)
        except (MigrationError, tomllib.TOMLDecodeError) as err:
            raise MigrationError(f"{manifest}: {err}") from None
        if package:
            packages.append(package)

    # Each `flux.toml` becomes a `.flux/config.toml` in the same directory, and settings from
    # manifests go to the one at the root
    configs = {flux_toml.parent: migrate_flux_toml(flux_toml, plan) for flux_toml in find_files(root, "flux.toml")}
    add_package_settings(configs.setdefault(root, Config()), packages)

    for dir, config in configs.items():
        if config.is_empty():
            continue
        path = dir / ".flux" / "config.toml"
        if path.exists():
            raise MigrationError(
                f"{path} already exists, merge the following into it by hand:\n{render_config(config)}"
            )
        plan.writes[path] = render_config(config)


def show(plan: Plan) -> None:
    for path, new_text in sorted(plan.writes.items()):
        old_text = path.read_text() if path.exists() else ""
        diff = difflib.unified_diff(
            old_text.splitlines(keepends=True),
            new_text.splitlines(keepends=True),
            fromfile=str(path) if old_text else "/dev/null",
            tofile=str(path),
        )
        sys.stdout.writelines(diff)
    for path in sorted(plan.deletes):
        print(f"delete {path}")


def apply(plan: Plan) -> None:
    for path, new_text in sorted(plan.writes.items()):
        action = "update" if path.exists() else "create"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(new_text)
        print(f"{action} {path}")
    for path in sorted(plan.deletes):
        path.unlink()
        print(f"delete {path}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Migrate a project from the old Flux configuration format to the current one."
    )
    parser.add_argument("paths", nargs="+", type=Path, help="root directories of the projects")
    parser.add_argument("--dry-run", action="store_true", help="show the changes without applying them")
    args = parser.parse_args()

    plan = Plan()
    try:
        for root in args.paths:
            plan_migration(root.resolve(), plan)
    except MigrationError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1

    if args.dry_run:
        show(plan)
    else:
        apply(plan)
    for warning in plan.warnings:
        print(f"warning: {warning}", file=sys.stderr)
    if not plan.writes and not plan.deletes:
        print("nothing to migrate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
