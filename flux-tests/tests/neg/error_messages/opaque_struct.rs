#![feature(register_tool)]
#![register_tool(flux)]

#[flux::opaque]
struct S {
    x: i32,
}

fn opaque_struct(s: S) -> i32 {
    s.x //~ ERROR opaque
}
