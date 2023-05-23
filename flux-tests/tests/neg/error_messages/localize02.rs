#![feature(register_tool)]
#![register_tool(flux)]
#![allow(unused)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn funky(x: int) -> bool {
        0 < x && (x < 10 && x % 2 == 0)
    }
}]

#[flux::sig(fn(x: i32{ funky(x) }))]
fn assertp(_x: i32) {}

fn test() {
    assertp(12);
}
