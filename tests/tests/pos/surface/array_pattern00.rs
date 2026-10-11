// A slice pattern on an array or slice lowers to a `ConstantIndex` projection. The fold/unfold
// analysis stops walking a place at an index projection and returns the prefix it reached, which
// used to trip an assertion in the elaboration pass when that prefix still needed unfolding.

use flux_attrs::*;

// Refinements on the element type survive the projection.
#[spec(fn(&[u8{v: v > 0}; 5]) -> u8{v: v > 0})]
pub fn second(src: &[u8; 5]) -> u8 {
    match src {
        [_, x, ..] => *x,
    }
}

// `ConstantIndex` counting from the end.
#[spec(fn(&[u8{v: v > 0}; 5]) -> u8{v: v > 0})]
pub fn last(src: &[u8; 5]) -> u8 {
    match src {
        [.., x] => *x,
    }
}

// Both ends of a slice at once.
#[spec(fn(&[u8{v: v > 0}]) -> u8{v: v > 0})]
pub fn first_of_two(src: &[u8]) -> u8 {
    match src {
        [x, .., _] => *x,
        _ => 1,
    }
}

// The pattern also constrains the length of a slice.
#[spec(fn(&[u8][@n]) -> usize{v: v <= n})]
pub fn len_at_least_two(src: &[u8]) -> usize {
    match src {
        [_, _, ..] => 2,
        _ => 0,
    }
}

// An array behind a field, so the place reaching it still needs unfolding. This is the shape
// that tripped the assertion.
#[refined_by(lo: int)]
pub struct S {
    #[field(u8[lo])]
    lo: u8,
    #[field([u8{v: v > lo}; 5])]
    a: [u8; 5],
}

#[spec(fn(&S[@lo]) -> u8{v: v > lo})]
pub fn field_second(s: &S) -> u8 {
    match &s.a {
        [_, x, ..] => *x,
    }
}

#[spec(fn(&S[@lo]) -> u8{v: v > lo})]
pub fn field_last(s: &S) -> u8 {
    match &s.a {
        [.., x] => *x,
    }
}
