#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(usize, usize{v : v > 0}) -> usize)]
pub fn assert_terminator_test(a: usize, b: usize) -> usize {
    let x = a / b;
    x
}
