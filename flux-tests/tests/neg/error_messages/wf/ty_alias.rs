#![feature(register_tool)]
#![register_tool(flux)]

#[flux::alias(type Gt(x: bool) = i32{v: v > x})] //~ ERROR mismatched sorts
type Gt = i32;
