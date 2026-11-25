#!/usr/bin/env python3
"""Writes the manifest of a nightly release.

Usage: nightly_manifest.py <dist-dir> <repo> <tag> <commit> <date>

<dist-dir> holds one `flux-<target>.tar.gz` archive per target, built by `cargo x dist`. The
manifest is written to `<dist-dir>/manifest.json`. The toolchain is read from the
`rust-toolchain.toml` in the current directory, i.e., the checkout of <commit>.
"""

import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path


def main() -> None:
    dist_dir, repo, tag, commit, date = sys.argv[1:]
    dist = Path(dist_dir)

    with open("rust-toolchain.toml", "rb") as f:
        toolchain = tomllib.load(f)["toolchain"]

    targets = {}
    for archive in sorted(dist.glob("flux-*.tar.gz")):
        target = re.fullmatch(r"flux-(.+)\.tar\.gz", archive.name)[1]
        targets[target] = {
            "url": f"https://github.com/{repo}/releases/download/{tag}/{archive.name}",
            "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
        }
    if not targets:
        sys.exit(f"no archives in {dist}")

    manifest = {
        "commit": commit,
        "date": date,
        "toolchain": {
            "channel": toolchain["channel"],
        },
        "targets": targets,
    }
    (dist / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
