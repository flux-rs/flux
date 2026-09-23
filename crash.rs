#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct S<T> {
    x: T,
}

pub enum E {
    A,
    B,
}

#[flux::spec(fn(&mut {n. S<i32{v: v <= n}>[n] | n >= 0}))]
fn foo(_: &mut S<i32>) {}

pub fn test(s: &mut S<i32>, e: E) -> i32 {
    match e {
        E::A => foo(s),
        E::B => {}
    }
    0
}
