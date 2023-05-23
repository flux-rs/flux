#![feature(register_tool)]
#![register_tool(flux)]
#![allow(unused)]
#![flux::defs {
    fn funky(x: int) -> bool {
        x > 0 && x < 10 && x % 2 == 0
    }
}]

#[flux::sig(fn(x: i32{ funky(x) }))]
fn assertp() {}

fn test() {
    assertp(11);
}
