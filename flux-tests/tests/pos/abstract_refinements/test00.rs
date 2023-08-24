#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(
    fn[p: int -> bool](x: i32, y: i32) -> i32{v: p(v) && v >= x && v >= y}
    requires p(x) && p(y)
)]
fn max(x: i32, y: i32) -> i32 {
    if x > y {
        x
    } else {
        y
    }
}

#[flux::sig(fn() -> i32{v: v % 2 == 0})]
fn test00() -> i32 {
    max(4, 10)
}

#[flux::sig(fn() -> i32[10])]
fn test01() -> i32 {
    max(4, 10)
}
