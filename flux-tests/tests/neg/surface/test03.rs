#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(
fn(x: &strg i32[@n]) -> i32
ensures x: i32[n]
)]
pub fn inc(x: &mut i32) -> i32 { //~ ERROR postcondition might not hold
    *x += 1;
    0
}
