# Known Issues

## cfg Parsing Issue with rustc nightly-2026-02-07 (efc9e1b50)

**Status**: Blocked on upstream cargo fix

**Issue**: When running `cargo xtask test`, the following error occurs:
```
error: failed to parse the cfg from `rustc --print=cfg`, got:
___
lib___.rlib
...
```

**Root Cause**:
- rustc commit efc9e1b50 (2026-02-06) introduced changes that affect how output is formatted when multiple `--print` options are used
- cargo (version fe2f314ae from 2026-01-30) calls rustc with `--crate-name ___` and multiple `--print` options
- The output includes `___` as a crate name and file names like `lib___.rlib`, which cargo's cfg parser cannot handle
- A fix for cargo was merged in commit 8b251d9 (2026-02-09) which properly handles the `___` delimiter
- However, this fix is not yet available in a released nightly toolchain compatible with rustc nightly-2026-02-07

**Attempted Solutions**:
1. ❌ Update cargo_metadata 0.23.0 → 0.23.1 and cargo-platform 0.3.1 → 0.3.2: Did not resolve the issue
2. ❌ Downgrade to rustc nightly-2026-02-05: Causes API incompatibility errors in flux-driver
3. ⏳ Waiting for a nightly release that includes both:
   - rustc with the necessary APIs that flux-driver depends on
   - cargo with the fix from commit 8b251d9

**Workaround**: None available currently. The project cannot run tests until upstream cargo is updated.

**References**:
- rustc commit: efc9e1b50cbf2cede7ebe25f0a1fc64fd8b3e942 (2026-02-06)
- cargo fix commit: 8b251d9541fd1dfef8600b992dcac9f2808caa6e (2026-02-09)
- cargo PR: rust-lang/cargo#16599

**Resolution**: Wait for next nightly release after 2026-02-09 that includes the cargo fix.
