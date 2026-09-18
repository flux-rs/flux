use flux_rs::attrs::*;

extern crate flux_core;

// The loop-head invariant is `i + size(iter) == size(s0)`, fixpoint can only synthesize that
// by instantiating a *higher-order* qualifier param with the constant for `size`.
// NOTE: the first param binds the kvar's value variable, so `x` must come first.
flux_rs::defs! {
    qualifier SzEqA(iter: int, size: int -> int, i: int, iter0: int) { i + size(iter) == size(iter0) }
    qualifier SzEqB(i: int, iter: int, size: int -> int, iter0: int) { i + size(iter) == size(iter0) }
}

#[trusted(reason = "spec")]
#[spec(fn (iter: &mut I[@curr]) -> Option<I::Item>[#some]
       ensures iter: I[#next],
               <I as Iterator>::step(curr, next),
               if !some { <I as Iterator>::size(curr) == 0 } else { <I as Iterator>::size(curr) > 0 && <I as Iterator>::size(next) == <I as Iterator>::size(curr) - 1 }
 )]
fn fake_next<I: Iterator>(iter: &mut I) -> Option<I::Item> {
    iter.next()
}

#[spec(fn(iter: I[@s], upper: usize) requires <I as Iterator>::size(s) <= upper)]
pub fn loop_fake_next<I: Iterator<Item = bool>>(mut iter: I, upper: usize) {
    let mut i = 0;
    while let Some(_) = fake_next(&mut iter) {
        flux_rs::assert(i < upper);
        i += 1;
    }
}

#[spec(fn(iter: I[@s], upper: usize) requires <I as Iterator>::size(s) <= upper)]
pub fn loop_next<I: Iterator<Item = bool>>(mut iter: I, upper: usize) {
    let mut i = 0;
    while let Some(_) = iter.next() {
        flux_rs::assert(i < upper);
        i += 1;
    }
}

#[spec(fn(iter: I[@s], upper: usize) requires <I as Iterator>::size(s) <= upper)]
pub fn loop_enumerate<I: Iterator<Item = bool>>(mut iter: I, upper: usize) {
    for (i, _) in iter.enumerate() {
        flux_rs::assert(i < upper);
    }
}
