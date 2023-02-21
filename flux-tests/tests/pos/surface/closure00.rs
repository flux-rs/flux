#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(c: Option<bool>) -> Option<i32>)]
pub fn test0(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 })
}
