#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::trusted]
#[flux::sig(
    fn(x: &strg T[@n], y: &strg T[@m])
    ensures x: T[m], y: T[n]
)]
fn swap<T>(x: &mut T, y: &mut T) {
    std::mem::swap(x, y)
}

fn test00() {
    let mut x = 0;
    let mut y = 1;
    swap(&mut x, &mut y);
    assert(x == 1);
    assert(y == 0);
}
