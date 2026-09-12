// An unknown associated refinement inside a `constant` annotation. This is
// resolved during conversion, so like the sort errors it only fires once
// something forces the constant's `constant_info`.

trait Tr {
    const B: bool;
}

#[flux::trusted]
#[flux::spec(fn() -> bool[A::B])]
fn get_b<A: Tr>() -> bool {
    true
}

struct S<T>(T);

impl<T> Tr for S<T> {
    #[flux::constant(T::not_a_reft())] //~ ERROR associated refinement not found
    const B: bool = false;
}

#[flux::spec(fn() -> bool[true])]
fn force_b<T>() -> bool {
    get_b::<S<T>>()
}
