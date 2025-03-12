#! /usr/bin/bash
#
# -----------------------------------------------------------------------------
# This script wraps `flux-driver` to collect performance profiling data for
# specific crates using Linux's perf tool (https://perfwiki.github.io/).
#
# Usage:
#   1. Set the `FLUX_DRIVER` environment variable to point to this script
#   2. Configure the `CRATES` variable below to list the crates you want to profile
#   3. Run `cargo flux` as normal, and this script will automatically
#      profile the specified crates
#
# The script will generate `{crate_name}-perf.data` files that can be analyzed with:
#   `perf report -i {crate_name}-perf.data`
# or any other analysis tool compatible with perf.
#
# Configuration:
#   - CRATES: Space-separated list of crate names to profile
#   - PERF_FLAGS: Array of flags passed to 'perf record' command
#     Default flags:
#       -F 997: Sample at 997 Hz (prime number close to 1000, reduces aliasing)
#       --call-graph dwarf,16384: Collect call-graph data using DWARF with 16K stack size
#       -g: Enable call-graph recording
# -----------------------------------------------------------------------------

# Specify the crate names to profile (space-separated). These are the name of the crates
# not the packages, i.e., the name of `[lib]` or a `[[bin]`.
CRATES="crate1 crate2"
# Configure perf sampling parameters
PERF_FLAGS=("-F" "997" "--call-graph" "dwarf,16384" "-g")

# This will guess the path of the real `flux-driver`. Adjust accordingly if necessary
export FLUX_SYSROOT="${FLUX_SYSROOT:-$HOME/.flux}"
export FLUX_DRIVER="${FLUX_SYSROOT}/flux-driver"

# Cargo reads for stdout so we must print to stderr
info() { echo "$@" 1>&2; }

# Parse arguments passed to `flux-driver` to find the crate name
args=("$@")
crate_name=""
for ((i = 0; i < ${#args[@]}; i++)); do
    if [[ "${args[i]}" == "--crate-name" && $((i+1)) -lt ${#args[@]} ]]; then
        crate_name="${args[i+1]}"
        break
    fi
done

if [[ -n "$crate_name" && " $CRATES " =~ .*\ $crate_name\ .* ]]; then
    # Run with perf if the current crate is in our target list
    info "Running Flux with 'perf' for crate: $crate_name"
    info "Command: $FLUX_DRIVER" "$@"
    timeout 60 perf record "${PERF_FLAGS[@]}" -o "$crate_name-perf.data" "$FLUX_DRIVER" "$@"
else
    # Run flux-driver normally for non-targeted crates
    "$FLUX_DRIVER" "$@"
fi
