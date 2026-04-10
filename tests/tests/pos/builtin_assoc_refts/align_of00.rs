use flux_rs::attrs::*;

#[repr(align(2))]
struct A(i8);

#[spec(fn() requires T::align_of() == 2)]
fn requires_align_2<T>() {}

#[spec(fn() requires T::align_of() < 16)]
fn requires_align_below_16<T>() {}

fn test01() {
    requires_align_2::<A>();
}

fn test02() {
    requires_align_below_16::<i64>();
}
