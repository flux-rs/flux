// Test that `axiom`s are only instantiated when their hypotheses hold

use flux_attrs::*;

defs! {
    fn modc(x: int, c: int) -> int;

    axiom ModPeriodic(x: int, y: int, c: int) {
        (c > 0 && y == x - c) => modc(y, c) == modc(x, c)
    }
}

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

#[trusted]
#[spec(fn(x: i32, c: i32) -> i32{v: v == modc(x, c)})]
fn modc(x: i32, c: i32) -> i32 {
    x.rem_euclid(c)
}

#[spec(fn(x: i32, c: i32))]
pub fn test(x: i32, c: i32) {
    let y = x - c;
    let z = y - c;
    // the axiom is triggered by pairs of `modc` terms, so the VC must mention `modc(y, c)`
    let a = modc(x, c);
    let _b = modc(y, c);
    let d = modc(z, c);
    assert(a == d); //~ ERROR refinement type
}
