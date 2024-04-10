struct S<'a> {
    #[flux::field(&i32{v : v > 0})]
    x: &'a i32,
}

#[flux::sig(fn(x: i32{x >= 0}))]
fn construct(x: i32) {
    let y = x + 1;
    let s = S { x: &y };
}

#[flux::sig(fn(x: S) -> i32{v : v > 0})]
fn project(s: S) -> i32 {
    *s.x + 1
}
