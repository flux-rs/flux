// Test that a `local axiom` is NOT used when checking a function that does not request it

use flux_attrs::*;

defs! {
    fn modc(x: int, c: int) -> int;

    local axiom ModPeriodic(x: int, y: int, c: int) {
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

#[axioms(ModPeriodic)]
#[spec(fn(x: i32, c: i32{c > 0}))]
pub fn test_with(x: i32, c: i32) {
    let y = x - c;
    let z = y - c;
    let a = modc(x, c);
    let _b = modc(y, c);
    let d = modc(z, c);
    assert(a == d);
}

#[spec(fn(x: i32, c: i32{c > 0}))]
pub fn test_without(x: i32, c: i32) {
    let y = x - c;
    let z = y - c;
    let a = modc(x, c);
    let _b = modc(y, c);
    let d = modc(z, c);
    assert(a == d); //~ ERROR refinement type
}
