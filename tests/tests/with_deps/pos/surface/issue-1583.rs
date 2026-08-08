// Proving `arr[i]` in bounds requires the invariant `end <= 10` on the range's `end` field, and
// `10` appears only as a literal, so the qualifier must have its parameter `a` instantiated with
// it. This does not verify without the `#` marker.
#![allow(unused)]
#![flux::defs {
    qualifier LeLit(x: int, a #: int) { x <= a }
}]

extern crate flux_core;

pub fn blah(arr: &[i32; 10]) -> i32 {
    let mut tot = 0;
    for i in 0..10 {
        tot += arr[i];
    }
    tot
}
