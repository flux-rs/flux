#![feature(register_tool)]
#![register_tool(flux)]
#![allow(unused)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn funky(x: int) -> bool {
        0 < x && (x < 10 && x % 2 == 0) //~ NOTE this is the condition
    }

    fn chunky(y:int) -> bool {
        funky(y) && 2 <= y
    }
}]

#[flux::sig(fn(x: i32{ chunky(x) }))] //~ NOTE inside this specifunction call
fn assertp(_x: i32) {}

fn test() {
    assertp(12); //~ ERROR precondition
                 //~| NOTE call site
                 //~| NOTE a precondition cannot be proved
}
