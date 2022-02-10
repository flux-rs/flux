// This only fails if we don't check for asserts
// ignore-test

#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(usize, usize) -> usize)]
pub fn assert_terminator_test(a: usize, b: usize) -> usize {
    let x = a / b;
    x
}
