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
    assert(x == 2); //~ ERROR precondition might not hold
    assert(y == 1); //~ ERROR precondition might not hold
}

#[flux::sig(fn(b: bool, x: T[@n], y: T[@m]) -> T[if b { n } else { m }])]
fn choose<T>(b: bool, x: T, y: T) -> T {
    if b {
        x
    } else {
        y
    }
}

fn test01() {
    assert(choose(false, 0, 1) == 0); //~ ERROR precondition might not hold
    assert(choose(true, 0, 1) == 1); //~ ERROR precondition might not hold
}
