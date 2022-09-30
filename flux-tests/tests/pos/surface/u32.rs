#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x:u32) -> u32{v: v > x})]
pub fn inc(x: u32) -> u32 {
    x + 1
}

pub type SboxPtr = i32;

#[flux::sig(fn(SboxPtr) -> bool[true])]
pub fn in_lin_mem(_ptr: SboxPtr) -> bool {
    true
}
