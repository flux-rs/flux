#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

pub struct S {
    #[lr::field(i32{v : v > 0})]
    a: i32,
    #[lr::field(i32)]
    b: i32,
}

pub fn baz(s: S) {}

pub fn foo() {
    let mut x = S { a: 1, b: 0 };
    x.a = 2;
    baz(x);
}
