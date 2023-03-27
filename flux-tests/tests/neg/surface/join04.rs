#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool) -> i32{v: v >= 0})]
fn ref_join(z: bool) -> i32 {
    let mut x = 0;
    let mut y = 1;

    let r = if z { &mut x } else { &mut y };
    *r = *r - 1;

    x //~ ERROR postcondition
}
