#![feature(register_tool)]
#![register_tool(flux)]

pub type S = i32;

#[flux::sig(fn(S))]
pub fn test00(x: S) {}

type MyResult1<T> = Result<T, i32>;

#[flux::sig(fn() -> MyResult1<i32{v: v > 0}>)]
fn test01() -> MyResult1<i32> {
    Ok(1)
}

type MyResult2<T> = Result<i32, T>;

#[flux::sig(fn() -> MyResult2<i32{v: v > 0}>)]
fn test02() -> MyResult2<i32> {
    Err(1)
}
