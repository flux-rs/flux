use flux_attrs::*;

#[spec(fn(&[u8{v: v > 0}; 5]) -> u8{v: v > 1})]
pub fn second(src: &[u8; 5]) -> u8 {
    match src {
        [_, x, ..] => *x, //~ ERROR refinement type
    }
}

#[spec(fn(&[u8{v: v > 0}; 5]) -> u8{v: v > 1})]
pub fn last(src: &[u8; 5]) -> u8 {
    match src {
        [.., x] => *x, //~ ERROR refinement type
    }
}

// The element refinement must come from the array, not be assumed.
#[spec(fn(&[u8; 5]) -> u8{v: v > 0})]
pub fn unrefined(src: &[u8; 5]) -> u8 {
    match src {
        [_, x, ..] => *x, //~ ERROR refinement type
    }
}

#[spec(fn(&[u8{v: v > 0}]) -> u8{v: v > 1})]
pub fn first_of_two(src: &[u8]) -> u8 {
    match src {
        [x, .., _] => *x, //~ ERROR refinement type
        _ => 2,
    }
}

// The pattern gives `n >= 2`, not `n > 2`.
#[spec(fn(&[u8][@n]) -> usize{v: v < n} requires n > 0)]
pub fn len_at_least_two(src: &[u8]) -> usize {
    match src {
        [_, _, ..] => 2, //~ ERROR refinement type
        _ => 0,
    }
}

#[refined_by(lo: int)]
pub struct S {
    #[field(u8[lo])]
    lo: u8,
    #[field([u8{v: v > lo}; 5])]
    a: [u8; 5],
}

#[spec(fn(&S[@lo]) -> u8{v: v > lo + 1})]
pub fn field_second(s: &S) -> u8 {
    match &s.a {
        [_, x, ..] => *x, //~ ERROR refinement type
    }
}

#[spec(fn(&S[@lo]) -> u8{v: v > lo + 1})]
pub fn field_last(s: &S) -> u8 {
    match &s.a {
        [.., x] => *x, //~ ERROR refinement type
    }
}
