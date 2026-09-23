#[flux::refined_by(n: T)]
pub struct S<T> {
    #[flux::field(T[n])]
    x: T,
}

#[flux::sig(fn() -> {n. S<i32{v: v <= n}>[n] | n >= 0})]
fn mk() -> S<i32> {
    S { x: 0 }
}

fn consume(_: S<i32>) {}

pub fn test(b: bool) {
    let s = if b { mk() } else { mk() };
    consume(s);
}
