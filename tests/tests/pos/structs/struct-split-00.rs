#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub struct S {
    #[flux::field(i32)]
    a: i32,
    #[flux::field(i32)]
    b: i32,
}

pub fn foo() {
    let mut x = S { a: 0, b: 1 };
    let r1 = &mut x.a;
    *r1 = 3;
    assert(x.a == 3);
}
