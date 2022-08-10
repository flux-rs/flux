#![feature(register_tool)]
#![register_tool(flux)]

pub enum Enum<T> {
    A(T),
    B(i64),
}

#[flux::sig(fn(Enum<i32{v : v >= 0}>) -> i32{v : v > 0})]
pub fn test(x: Enum<i32>) -> i32 {
    let y = match x {
        Enum::A(n) => n,
        Enum::B(_) => 0,
    };
    // test we correctly join branches with different variants
    y + 1
}
