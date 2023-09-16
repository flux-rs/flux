#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

#[flux::sig(fn() -> i32{v : v > 0})]
pub fn tuple00() -> i32 {
    let t = (-3, 2);
    t.0 + t.1 //~ ERROR refinement type
}

#[flux::sig(fn(i32) -> i32[0])]
pub fn tuple01(x: i32) -> i32 {
    let t = (x, x + 1);
    t.1 - t.0 //~ ERROR refinement type
}

#[flux::sig(fn(i32[@n]) -> i32[n+1])]
pub fn tuple02(mut x: i32) -> i32 {
    let t = (&mut x, 0);
    *t.0 += t.1;
    x //~ ERROR refinement type
}
