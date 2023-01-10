#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(i32[0asd]))] //~ ERROR invalid suffix `asd` for number literal
fn test00(x: i32) {}
