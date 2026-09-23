#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct S<T> {
    x: T,
}

#[flux::trusted]
#[flux::sig(fn() -> {n. S<i32{v: v <= n}>[n] | n >= 0})]
fn mk() -> S<i32> {
    S { x: 0 }
}

fn consume(_: S<i32>) {}

pub fn test(b: bool) {
    let s = if b { mk() } else { mk() };
    consume(s);
}
