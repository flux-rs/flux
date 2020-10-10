# Build instructions

After installing rustup, run the following commands:
```bash
rustup override set nightly-2020-10-09
rustup component add rust-src llvm-tools-preview
```

Then, build the project using `cargo build`.

# Usage
You can use `cargo run <file>` to compile any Rust source code file.
