#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(b:bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(b:bool) ensures b)]
pub fn assume(b: bool) {
    if !b {
        panic!("assume fails")
    }
}

#[flux::sig(fn(x:i32))]
pub fn dec(x: i32) {
    assume(x > 10);
    assert(x > 0);
    assert(x > 20); //~ ERROR refinement type

}
