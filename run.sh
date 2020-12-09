#!/bin/sh

rm -f output.fq

cargo run "$@"

if [[ $? -eq 0 ]]; then
    fixpoint output.fq
fi
