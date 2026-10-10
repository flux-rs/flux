use flux_attrs::*;

pub trait Trait {
    type Item;
}

impl Trait for () {
    type Item = u8;
}

impl Trait for bool {
    type Item = u16;
}

impl<T> Trait for Vec<T> {
    type Item = T;
}

// Refinements are still checked when the Rust signature has a projection.
#[spec(fn() -> u8{v: v > 0})]
pub fn get_pos() -> <() as Trait>::Item {
    0 //~ ERROR refinement type
}

// Refinements dropped when normalizing for the comparison are still checked.
#[spec(fn() -> <Vec<u8{v: v > 0}> as Trait>::Item)]
pub fn bad() -> u8 {
    0 //~ ERROR refinement type
}

// The projection normalizes to a type that doesn't match.
#[spec(fn() -> <() as Trait>::Item)] //~ ERROR incompatible refinement annotation
pub fn wrong() -> u16 {
    0
}

// Both projections normalize, but to different types.
#[spec(fn() -> <() as Trait>::Item)] //~ ERROR incompatible refinement annotation
pub fn alias_alias() -> <bool as Trait>::Item {
    0
}
