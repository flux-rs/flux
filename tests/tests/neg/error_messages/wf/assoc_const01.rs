// An ill-sorted expression inside a `constant` annotation on an associated
// constant. As in assoc_const00.rs, the annotation is only checked once
// something forces the constant's `constant_info`.

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
    #[flux::constant(1 + true)] //~ ERROR mismatched sorts
    const N: i32 = 0;

    // `T::size_of()` is an `int`, not a `bool`.
    #[flux::constant(T::size_of())] //~ ERROR mismatched sorts
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
