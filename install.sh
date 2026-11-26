#!/bin/sh
# Installs the latest prebuilt Flux:
#
#     curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/flux-rs/flux/main/install.sh | sh
#
# To install a given release instead, e.g., `nightly-2026-11-20`, pass `-s -- --to <tag>` to `sh`.
#
# The script downloads and extracts the release archive for this platform, and then runs
# `cargo flux self install` from it, which does the actual installation. Once installed, Flux is
# updated with `cargo flux self update`.

set -eu

RELEASES_URL="https://github.com/flux-rs/flux/releases/download"
INSTALL_GUIDE_URL="https://flux-rs.github.io/flux/guide/install.html"

err() {
    echo "error: $*" >&2
    exit 1
}

need() {
    command -v "$1" > /dev/null 2>&1 || err "$1 is required to install Flux${2:-}"
}

tag=nightly
while [ $# -gt 0 ]; do
    case "$1" in
        --to)
            [ $# -ge 2 ] || err "--to needs a release tag, e.g., nightly-2026-11-20"
            tag=$2
            shift 2
            ;;
        *) err "unknown argument $1" ;;
    esac
done

# Keep in sync with the `build` job of .github/workflows/nightly.yml.
case "$(uname -s)-$(uname -m)" in
    Linux-x86_64) target=x86_64-unknown-linux-gnu ;;
    Darwin-arm64) target=aarch64-apple-darwin ;;
    MINGW* | MSYS* | CYGWIN*) err "use install.ps1 in PowerShell to install Flux on Windows, see $INSTALL_GUIDE_URL" ;;
    *) err "there are no Flux releases for $(uname -s) $(uname -m), see $INSTALL_GUIDE_URL to build it from source" ;;
esac

need curl
need tar
need rustup ", see https://rustup.rs"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

archive="flux-$target.tar.gz"
echo "Downloading $RELEASES_URL/$tag/$archive"
curl --proto '=https' --tlsv1.2 -fsSL --retry 3 -o "$tmp/$archive" "$RELEASES_URL/$tag/$archive" ||
    err "failed to download the release $tag, the releases are listed in https://github.com/flux-rs/flux/releases"
tar -xzf "$tmp/$archive" -C "$tmp"

"$tmp/sysroot/bin/cargo-flux" flux self install
