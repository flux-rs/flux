use flux_rs::attrs::*;

#[repr(align(4))]
struct A(bool);

#[spec(fn() requires T::align_of() == 2)]
fn requires_align_2<T>() {}

#[spec(fn() requires T::align_of() > 16)]
fn requires_align_above_16<T>() {}

fn test01() {
    requires_align_2::<A>(); //~ ERROR refinement type
}

fn test02() {
    requires_align_above_16::<i64>(); //~ ERROR refinement type
}
