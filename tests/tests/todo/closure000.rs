#[flux::sig(fn (i32{v: 0 <= v}) -> i32{v: 0 < v})]
fn foo(x: i32) -> i32 {
    x + 1
}

fn test() -> Vec<i32> {
    (0..10).map(|i| foo(i)).collect()
}
