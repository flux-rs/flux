#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
pub fn assert(_: bool) {}

#[flux::sig(async fn(n:i32) -> i32{v: n <= v})]
pub async fn make_nat(n: i32) -> i32 {
    n + 1
}

#[flux::sig(async fn (y:i32) -> i32{v:y<=v} requires 0 <= y)]
pub async fn bar(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    y + z
}

#[flux::sig(async fn (k:i32) -> i32{v:k<=v} requires 0 <= k)]
pub async fn jazz(k: i32) -> i32 {
    let apple = bar(k).await;
    let banana = bar(apple).await;
    banana
}
