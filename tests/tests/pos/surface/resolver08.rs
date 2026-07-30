//! Test that `_` is never treated as a duplicate definition (matching rustc).
#![allow(dead_code)]

const _: i32 = 0;
const _: i32 = 0;
const _: i32 = 0;

mod nested {
    const _: i32 = 0;
    const _: i32 = 0;
}
