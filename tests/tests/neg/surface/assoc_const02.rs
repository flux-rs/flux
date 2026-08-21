//@ignore-test: unsound until `ConstDefId` carries generic args (step 3)

// `T::C` and `U::C` are associated constants of two unrelated types, so nothing
// relates their values. Until `ConstDefId` carries the trait ref's generic
// arguments, every instantiation of an associated constant converts to the same
// symbol and this is wrongly accepted.

trait Tr {
    const C: bool;
}

#[flux::trusted]
#[flux::spec(fn() -> bool[T::C])]
fn get<T: Tr>() -> bool {
    true
}

#[flux::spec(fn() -> bool[U::C])]
fn bad<T: Tr, U: Tr>() -> bool {
    get::<T>() //~ ERROR refinement type
}
