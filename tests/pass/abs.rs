#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty(fn (x: isize) -> {b: isize | b > 0isize})]
pub fn abs(x: isize) -> isize {
    if x > 0 {
        x
    } else {
        -x
    }
}
