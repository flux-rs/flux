#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> [i32{v : v > 0}; 20])] //~ ERROR array length mismatch
pub fn array00() -> [i32; 2] {
    [10, 11] 
}

