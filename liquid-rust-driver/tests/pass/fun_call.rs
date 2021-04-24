#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(n: int) -> {v: int | v == n + 1}")]
fn add1(n: i32) -> i32 {
    n + 1
}

#[liquid::ty("fn(n: int) -> {v: int | v == n + 2}")]
fn add2(n: i32) -> i32 {
    add1(add1(n))
}

#[liquid::ty("fn(n: {int | n >= 0}) -> {v: int | v >= n}")]
fn sum(n: i32) -> i32 {
    if n <= 0 {
        n
    } else {
        n + sum(n - 1)
    }
}
