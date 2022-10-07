#!/bin/bash

# Path to root of flux repository
FLUX=/Users/rjhala/research/rust/flux

CWD=`pwd`
cd $FLUX
TOOLCHAIN=`rustup show active-toolchain | cut -d' ' -f 1`

cd "$CWD"
rustup run "$TOOLCHAIN" cargo run --manifest-path "$FLUX/Cargo.toml" -- $@

