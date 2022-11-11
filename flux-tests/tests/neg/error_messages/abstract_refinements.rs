#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(
    fn<p: int -> bool>(x: i32) -> i32{v: p(v)}
    requires x > 0 || p(x) //~ ERROR illegal use of refinement parameter
)]
fn test00(x: i32) -> i32 {
    0
}

#[flux::sig(
    fn<p: int -> bool>(x: i32) -> i32{v: p(v)}
    requires p == p //~ ERROR illegal use of refinement parameter
    //~^ ERROR illegal use of refinement parameter
)]
fn test01(x: i32) -> i32 {
    0
}
