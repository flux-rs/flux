# Editor Support

## Rust-Analyzer in VSCode

Add this to the workspace settings i.e. `.vscode/settings.json` using in the appropriate paths for

* `DYLD_FALLBACK_LIBRARY_PATH` (on `macos`) or `LD_LIBRARY_PATH` (on `linux`)
* `RUSTC_WRAPPER`
* `RUSTUP_TOOLCHAIN` (should be the same as the contents of `/path/to/flux/rust-toolchain.toml`)

```json
{
  "rust-analyzer.checkOnSave.extraEnv": {
    "RUSTC_WRAPPER": "/path/to/flux/target/release/flux",
    "RUSTUP_TOOLCHAIN": "nightly-2022-10-11",
    "LD_LIBRARY_PATH": "/path/to/.rustup/toolchains/nightly-2022-10-11-x86_64-apple-darwin/lib"
  }
}
```

**Note:** Make sure to edit the paths in the above snippet to point to the correct locations on your machine.