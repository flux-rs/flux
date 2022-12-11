#![feature(register_tool)]
#![register_tool(flux)]

#[flux::opaque]
struct S {
    #[flux::field(i32[0])] //~ ERROR opaque struct can't have field annotations
    x: i32,
}
