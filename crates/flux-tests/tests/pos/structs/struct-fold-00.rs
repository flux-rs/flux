#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub struct S {
    #[flux::field(i32{v : v > 0})]
    a: i32,
    #[flux::field(i32)]
    b: i32,
}

pub fn baz(s: S) {}

pub fn foo() {
    let mut x = S { a: 1, b: 0 };
    x.a = 2;
    baz(x);
}
