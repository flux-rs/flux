#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(&mut i32[0], bool) -> i32[1])]
pub fn foo(r1: &mut i32, b: bool) -> i32 {
    let mut x = 1;
    let r;
    if b {
        r = &mut *r1;
    } else {
        r = &mut x;
    }
    *r //~ ERROR refinement type
}
