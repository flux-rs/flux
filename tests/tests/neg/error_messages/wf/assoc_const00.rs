// The refinement value given by `constant` must have the sort of the constant's
// type. Note the annotation is only checked once something forces the constant's
// `constant_info`, hence the `force_*` functions below.

trait Tr {
    const N: i32;
    const B: bool;
}

#[flux::trusted]
#[flux::spec(fn() -> i32[A::N])]
fn get_n<A: Tr>() -> i32 {
    0
}

#[flux::trusted]
#[flux::spec(fn() -> bool[A::B])]
fn get_b<A: Tr>() -> bool {
    true
}

struct S<T>(T);

impl<T> Tr for S<T> {
    #[flux::constant(true)] //~ ERROR mismatched sorts
    const N: i32 = 0;

    #[flux::constant(0)] //~ ERROR mismatched sorts
    const B: bool = false;
}

#[flux::spec(fn() -> i32[0])]
fn force_n<T>() -> i32 {
    get_n::<S<T>>()
}

#[flux::spec(fn() -> bool[true])]
fn force_b<T>() -> bool {
    get_b::<S<T>>()
}
