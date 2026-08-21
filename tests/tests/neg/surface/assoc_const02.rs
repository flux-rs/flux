// `T::C` and `U::C` are associated constants of two unrelated types, so nothing
// relates their values. This is only rejected because `ConstDefId` carries the
// trait ref's generic arguments; without them every instantiation of an
// associated constant would convert to the same symbol.

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
