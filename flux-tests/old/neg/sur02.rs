#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x: &mut n@i32) -> i32; x: i32{v: v == n + 1})]
pub fn inc(x: &mut i32) -> i32 { //~ ERROR postcondition might not hold
    *x += 2;
    0
}
