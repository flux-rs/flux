# lib

Crates in this directory are meant to be used as dependencies for projects using Flux. They should be
eventually published to [crates.io](https://crates.io). As such, they should not depend on other
crates in the workspace. They could live in a separate repository or be excluded from the workspace,
but we keep them inside to reuse `Cargo.lock` and the lint table.

## FLUX_BUILD_SYSROOT

These libraries behave differently depending on whether they are being used during normal compilation
or while flux is analyzing the code. For example, some macros are a no-op during normal compilation.
The different behavior is toggled with a `--cfg flux_sysroot` flag. We control the toggle from cargo
by setting the `FLUX_BUILD_SYSROOT` environment variable. This variable is read from the build scripts
which set the `--cfg flux_sysroot` when present.
