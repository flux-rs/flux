// Names inside a `constant` annotation on an associated constant are resolved
// eagerly, so this fires even though nothing mentions the constant.

trait Tr {
    const N: i32;
}

struct S<T>(T);

impl<T> Tr for S<T> {
    #[flux::constant(not_a_name)] //~ ERROR cannot find value `not_a_name` in this scope
    const N: i32 = 0;
}
