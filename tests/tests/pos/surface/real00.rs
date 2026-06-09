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
#[flux::sig(fn(x: Real) -> Real[x + 1.0])]
fn add1(x: Real) -> Real {
    Real
}

fn test01(x: Real) {
    #[flux::sig(fn(x: Real, y: Real{y > x}))]
    fn assert(x: Real, y: Real) {}

    assert(x, add1(x))
}

fn test02() {
    #[flux::sig(fn() requires 1.0/2.0 != 1.0/3.0)]
    fn assert() {}
    assert()
}
