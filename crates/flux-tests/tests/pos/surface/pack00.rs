fn bar() -> i32 {
    0
}

#[flux::sig(fn(bool))]
pub fn foo(b: bool) {
    let _x;
    if b {
    } else {
        _x = bar();
    }
}
