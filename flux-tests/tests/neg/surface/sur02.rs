#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1])]
pub fn inc(x: &mut i32) {
    *x += 2 //~ ERROR refinement type error
}
