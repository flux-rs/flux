use std::mem::swap;

use flux_rs::{assert, attrs::*, extern_spec};

#[extern_spec(std::mem)]
#[spec(fn(x: &mut T[@vx], y: &mut T[@vy]) ensures x: T[vy], y: T[vx])]
fn swap<T>(a: &mut T, b: &mut T);

pub fn test_swap() {
    let mut x = 5;
    let mut y = 10;
    swap(&mut x, &mut y);
    assert(x == 10);
    assert(y == 5);
    assert(y == 10); //~ ERROR refinement type
}
