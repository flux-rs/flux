#!/usr/bin/env bash
set -euo pipefail
BIN="$HOME/.cargo/bin"; mkdir -p "$BIN"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) Z3=x64-glibc; FP=fixpoint-x86_64-linux-gnu.tar.gz ;;
  Darwin-arm64) Z3=arm64-osx; FP=fixpoint-aarch64-apple-darwin.tar.gz ;;
  *) echo "no prebuilt z3+fixpoint for this platform" >&2; exit 1 ;;
esac

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT

# z3 (latest release)
url=$(curl -fsSL https://api.github.com/repos/Z3Prover/z3/releases/latest \
      | grep -o "https://[^\"]*-$Z3[^\"]*\.zip" | head -1)
curl -fsSL "$url" -o "$tmp/z3.zip"
unzip -qo "$tmp/z3.zip" -d "$tmp"
install -m755 "$tmp"/z3-*/bin/z3 "$BIN/z3"

# fixpoint (nightly prebuilt)
curl -fsSL "https://github.com/ucsd-progsys/liquid-fixpoint/releases/download/nightly/$FP" | tar xz -C "$BIN"
chmod +x "$BIN/fixpoint"

# flux (from source)
git clone --depth 1 https://github.com/flux-rs/flux "$tmp/flux"
( cd "$tmp/flux" && cargo xtask install )

echo "done: $("$BIN/z3" --version); fixpoint+flux in $BIN"
