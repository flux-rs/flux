#![feature(register_tool)]
#![register_tool(flux)]

#[flux::opaque]
#[flux::refined_by(r: real)]
#[derive(Clone, Copy)]
struct Real;

#[flux::trusted]
#[flux::sig(fn(x: Real, y: Real) -> Real[x + y])]
fn add(x: Real, y: Real) -> Real {
    Real
}

#[flux::trusted]
#[flux::sig(fn(x: Real) -> Real[x + 1real])]
fn add1(x: Real) -> Real {
    Real
}

#[flux::sig(fn(x: Real, y: Real{y > x}))]
fn assert_gt(x: Real, y: Real) {}

fn test(x: Real) {
    assert_gt(x, add1(x))
}
