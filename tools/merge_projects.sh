#!/usr/bin/env bash
# merge_projects.sh <lean_bench_dir> <output_dir>
#
# Merges all lean_proofs sub-projects under <lean_bench_dir> into a single
# Lake project at <output_dir>. Each test is re-namespaced from LeanProofs.*
# to <Category>.<Testname>.* to avoid collisions.
set -euo pipefail

BENCH_DIR="${1:?Usage: $0 <lean_bench_dir> <output_dir>}"
OUT_DIR="${2:?Usage: $0 <lean_bench_dir> <output_dir>}"

BENCH_DIR="$(cd "$BENCH_DIR" && pwd)"

if [[ -e "$OUT_DIR" ]]; then
  echo "Error: output directory '$OUT_DIR' already exists." >&2
  exit 1
fi
mkdir -p "$OUT_DIR"

# Convert a directory name (possibly hyphenated) to PascalCase Lean module name.
to_pascal() {
  local s="$1"
  # Replace hyphens and underscores with spaces, capitalize each word, remove spaces.
  echo "$s" | sed 's/[-_]/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1)) substr($i,2); print}' | tr -d ' '
}

root_imports=()

for category_dir in "$BENCH_DIR"/*/; do
  category="$(basename "$category_dir")"
  cat_pascal="$(to_pascal "$category")"

  for test_dir in "$category_dir"*/; do
    [[ -d "$test_dir" ]] || continue
    src="$test_dir/lean_proofs"
    [[ -d "$src/LeanProofs/Flux" ]] || continue

    testname="$(basename "$test_dir")"
    test_pascal="$(to_pascal "$testname")"

    # Namespace: Category.Testname (e.g. AbstractRefinements.Test00)
    ns="${cat_pascal}.${test_pascal}"
    # Filesystem prefix inside OUT_DIR (e.g. AbstractRefinements/Test00)
    ns_path="${cat_pascal}/${test_pascal}"

    dest="$OUT_DIR/$ns_path"
    mkdir -p "$dest"

    # Copy all .lean files from LeanProofs/ tree, rewriting imports.
    while IFS= read -r -d '' f; do
      # Path relative to src/LeanProofs/
      rel="${f#$src/LeanProofs/}"
      out_file="$dest/$rel"
      mkdir -p "$(dirname "$out_file")"
      # Rewrite: import LeanProofs.X  →  import <ns>.X
      sed "s/import LeanProofs\./import ${ns}./g" "$f" > "$out_file"
    done < <(find "$src/LeanProofs" -name '*.lean' -print0)

    # Write the root module file for this test (mirrors LeanProofs.lean → <ns>.lean)
    # It just imports <ns>.Basic
    root_file="$OUT_DIR/${ns_path%/*}/${test_pascal}.lean"
    printf 'import %s.Basic\n' "$ns" > "$root_file"

    root_imports+=("$ns")
  done
done

# Write the top-level AllProofs.lean that imports every test root.
all_file="$OUT_DIR/AllProofs.lean"
{
  for ns in "${root_imports[@]}"; do
    echo "import $ns"
  done
} > "$all_file"

# Collect the distinct top-level namespaces (one per category).
mapfile_categories=()
while IFS= read -r d; do
  mapfile_categories+=("$(basename "$d")")
done < <(find "$OUT_DIR" -mindepth 1 -maxdepth 1 -type d | sort)

# Write lakefile.toml — same toolchain and LeanFixpoint dep as all sub-projects.
# Adjust the LeanFixpoint path if needed.
LEAN_FIXPOINT_PATH="/Users/petros/Documents/UCSD/Work/lean-fixpoint"

{
  cat <<TOML
name = "lean_bench_all"
version = "0.1.0"
defaultTargets = ["LeanBenchAll"]

[[lean_lib]]
name = "LeanBenchAll"
roots = ["AllProofs"]
globs = [
  "AllProofs",
TOML
  for cat in "${mapfile_categories[@]}"; do
    echo "  \"${cat}.**\","
  done
  cat <<TOML
]

[[require]]
name = "LeanFixpoint"
path = "${LEAN_FIXPOINT_PATH}"
TOML
} > "$OUT_DIR/lakefile.toml"

# Create stub root .lean files for each category so Lake's ** globs work.
for cat in "${mapfile_categories[@]}"; do
  stub="$OUT_DIR/${cat}.lean"
  [[ -f "$stub" ]] || printf '' > "$stub"
done

# Copy the toolchain file from the first sub-project found.
first_toolchain="$(find "$BENCH_DIR" -name lean-toolchain -not -path '*/.lake/*' | { IFS= read -r line; echo "$line"; cat > /dev/null; })"
cp "$first_toolchain" "$OUT_DIR/lean-toolchain"

# Copy the lake-manifest from the first sub-project so Lake doesn't need to
# re-resolve the transitive deps (aesop, batteries) from scratch.
first_manifest="$(find "$BENCH_DIR" -name lake-manifest.json -not -path '*/.lake/*' | { IFS= read -r line; echo "$line"; cat > /dev/null; })"
cp "$first_manifest" "$OUT_DIR/lake-manifest.json"

echo "Done. Combined project written to: $OUT_DIR"
echo "  Root module : AllProofs"
echo "  Tests merged: ${#root_imports[@]}"
