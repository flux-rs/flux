#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x: &strg i32[@n]) -> () ensures x: i32[n])]
pub fn inc(x: &mut i32) {
    *x += 1 //~ ERROR postcondition might not hold
}
