#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct S<T> {
    x: T,
}

pub enum E {
    A,
    B,
}

#[flux::trusted]
#[flux::sig(fn() -> {n. S<i32{v: v <= n}>[n] | n >= 0})]
fn mk() -> S<i32> {
    S { x: 0 }
}

#[flux::spec(fn(&mut {n. S<i32{v: v <= n}>[n] | n >= 0}))]
fn foo(_: &mut S<i32>) {}

#[flux::spec(fn(&mut {n. S<i32{v: v <= n}>[n] | n > 0}))]
fn bar(_: &mut S<i32>) {}

pub fn test(e: E) -> i32 {
    let mut s = mk();
    match e {
        E::A => foo(&mut s),
        E::B => {}
    }
    bar(&mut s); //~ ERROR refinement type
    0
}
