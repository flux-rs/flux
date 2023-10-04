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

fn test01(x: Real) {
    #[flux::sig(fn(x: Real, y: Real{y > x}))]
    fn assert(x: Real, y: Real) {}

    assert(add1(x), x) //~ ERROR refinement type
}

fn test02() {
    #[flux::sig(fn() requires 1real/2real != 1real/2real)]
    fn assert() {}
    assert() //~ ERROR refinement type
}
