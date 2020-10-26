# Build instructions

After installing rustup, run the following commands:
```bash
rustup override set nightly-2020-10-09
rustup component add rust-src rustc-dev llvm-tools-preview
```

Then, build the project using `cargo build`.

# Usage

## To compile a single file

You can use `cargo run <file>` to compile any Rust source code file.

## To compile a whole cargo project

1. Compile a release build of `liquid-rust` running `cargo build --release`.

2. Locate the `rustc_driver` dynamic library. It should be located at `~/.rustup/toolchains/nightly-2020-10-09-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/lib/`.

3. Create an executable shell script with the following contents:
    ```bash
    #!/bin/sh
    LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<PATH_FOUND_IN_2> <PATH_TO_THIS_PROJECT>/target/release/liquid-rust "$@"
    ```
    Be sure the script has execution permission.

4. Inside the project where you want to use this compiler, create a `.cargo/config.toml` file with the following contents:
    ```toml
    [build]
    rustc = "<PATH_TO_THE_SCRIPT_FROM_3>"
    ```

5. Use `cargo build` normally with the target project.
