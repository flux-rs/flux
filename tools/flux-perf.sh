#! /usr/bin/bash
#
# --------------------------------------------------------------------------------------------
# This script wraps `flux-driver` to collect performance profiling data for
# specific crates using Linux's perf tool (https://perfwiki.github.io/).
#
# Usage:
#   1. Set the `FLUX_DRIVER` environment variable to point to this script
#   2. Configure the `CRATES` variable below to list the crates you want to profile
#   3. Run `cargo flux` as normal, and this script will automatically profile Flux when
#      checking the specified crates
#
# The script will generate `{crate_name}-perf.data` files that can be analyzed with:
#   `perf report -i {crate_name}-perf.data`
# or any other analysis tool compatible with perf. It will also generate a textual version
# that can be open with the Firefox profiler. If `rustfilt` is present it will also demangled
# names that were not present in the debug info.
#
# Configuration:
#   - CRATES: Space-separated list of crate names to profile
#   - PERF_FLAGS: Array of flags passed to 'perf record' command
#          Default flags:
#            -F 997: Sample at 997 Hz (prime number close to 1000)
#            --call-graph dwarf,16384: Collect call-graph data using DWARF with 16K stack size
#            -g: Enable call-graph recording
#            -z: Compress the perf data file output
#   - TIMEOUT: Run profiled process for specified duration and then terminate it. Prevents
#              hanging or excessively long-running processes. Set to 0 to disable timeout.
# --------------------------------------------------------------------------------------------

# Specify the crate names to profile (space-separated). These are crate names not packages, i.e.,
# the name of `[lib]` or a `[[bin]`.
CRATES="crate1 crate2"
# Configure perf sampling parameters
PERF_FLAGS=("-F" "997" "--call-graph" "dwarf,16384" "-g" "-z")
# Set timeout to prevent process from running too long
TIMEOUT=1m

# This will guess the path of the real `flux-driver`. Adjust accordingly if necessary
export FLUX_SYSROOT="${FLUX_SYSROOT:-$HOME/.flux}"
export FLUX_DRIVER="${FLUX_SYSROOT}/flux-driver"

# Cargo reads for stdout so we must print to stderr
info() { echo "$@" 1>&2; }

rename_if_exists() {
    local file="$1"

    if [[ -e "$file" ]]; then
        local rand_str
        rand_str=$(head /dev/urandom | tr -dc 'a-zA-Z0-9' | head -c 6)
        local new_file="${file}.old.${rand_str}"
        mv "$file" "$new_file"
    fi
}

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
    info "Running Flux with 'perf' for crate: $crate_name"
    info "Command: $FLUX_DRIVER" "$@"
    rename_if_exists "${crate_name}-perf.data"
    timeout $TIMEOUT perf record "${PERF_FLAGS[@]}" -o "${crate_name}-perf.data" "$FLUX_DRIVER" "$@"
    status=$?

    info "Converting perf data to text format: ${crate_name}.perf"
    rename_if_exists "${crate_name}.perf"
    perf script -F +pid -i "${crate_name}-perf.data" > "${crate_name}.perf"

    if command -v rustfilt >/dev/null 2>&1; then
        info "Demangling Rust symbols: $crate_name-demangled.perf"
        rename_if_exists "${crate_name}-demangled.perf"
        rustfilt -i "${crate_name}.perf" -o "${crate_name}-demangled.perf"
    fi
    exit $status
else
    "$FLUX_DRIVER" "$@"
fi
