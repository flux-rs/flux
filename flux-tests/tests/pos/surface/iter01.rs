#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

#[flux::sig(fn(Vec<i32{v:0<=v}>) -> ())]
pub fn test_loop(vec: Vec<i32>) {
    for val in vec.iter() {
        assert(0 <= *val)
    }
}
