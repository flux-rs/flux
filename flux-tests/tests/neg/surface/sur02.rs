#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(
fn(x: &strg i32[@n]) -> i32
ensures x: i32[n+1]
)]
pub fn inc(x: &mut i32) -> i32 { //~ ERROR postcondition might not hold
    *x += 2;
    0
}
