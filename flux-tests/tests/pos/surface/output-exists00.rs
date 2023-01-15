#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> (i32[#n], i32{v: v > n}))]
fn test00() -> (i32, i32) {
    (0, 1)
}

#[flux::sig(fn() -> i32{v: v > 0})]
fn test02() -> i32 {
    let (a, b) = test00();
    b - a
}
