#!/bin/sh

rm -f output.fq

cargo run "$@" -O

if [[ $? -eq 0 ]]; then
    fixpoint output.fq
fi
