# Editor Support

This section assumes you have installed `flux`, `cargo-flux`, and `rustc-flux`.

## Rust-Analyzer in VSCode

Add this to the workspace settings i.e. `.vscode/settings.json`

```json
{
  "rust-analyzer.checkOnSave.overrideCommand": [
    "cargo-flux",
    "check",
    "--workspace",
    "--message-format=json"
  ]
}
```

If you want to change the `flux` used by `cargo-flux`, then also specify the
`FLUX_PATH` like in the example below, which uses the version generated when you
run `cargo build`.

``` json
{
  "rust-analyzer.checkOnSave.extraEnv": {
    "FLUX_PATH": "/path/to/flux-repo/target/debug/flux",
  }
}
```

**Note:** Make sure to edit the paths in the above snippet to point to the correct locations on your machine.
