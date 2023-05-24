#![feature(register_tool)]
#![register_tool(flux)]

// Test use of constant in fn-signature

#[flux::constant]
pub const FORTY_TWO: usize = 21 + 21;

#[flux::sig(fn() -> usize{v: v < FORTY_TWO})]
pub fn test1() -> usize {
    13 + 50 //~ ERROR refinement type
}
