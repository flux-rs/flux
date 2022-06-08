#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

pub struct S {
    #[lr::field(i32)]
    a: i32,
    #[lr::field(i32)]
    b: i32,
}

pub fn foo() {
    let mut x = S { a: 0, b: 1 };
    let r1 = &mut x.a;
    *r1 = 0;
    assert(x.a > 0); //~ ERROR precondition might not hold
}
