use flux_rs::*;

#[sig(fn(x: i32{x != 0}) -> i32[1/x])]
fn div(x: i32) -> i32 {
    1 / x
}

fn apply<A, B>(f: impl FnOnce(A) -> B, x: A) -> B {
    f(x)
}

#[sig(fn() -> i32[0])]
fn test() -> i32 {
    apply(div, 10)
}
