#![feature(register_tool)]
#![register_tool(lr)]

// Note: only fails if line 329 of liquid-rust-typeck/src/checker.rs is uncommented
#[lr::ty(fn(usize, usize) -> usize)]
pub fn assert_terminator_test(a: usize, b: usize) -> usize {
    let x = a / b;
    x
}
