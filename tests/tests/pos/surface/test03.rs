#[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1])]
pub fn inc(x: &mut i32) {
    *x += 1;
}

#[flux::sig(fn() -> i32[1])]
pub fn test_inc() -> i32 {
    let mut x = 0;
    inc(&mut x);
    x
}
