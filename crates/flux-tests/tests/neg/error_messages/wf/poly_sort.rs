use std::hash::Hash;
#[flux::opaque]
#[flux::refined_by(elems: Set<Tiger>)] //~ ERROR cannot find sort `Tiger`
pub struct Foo<T> {
    pub inner: std::collections::HashSet<T>,
}

#[flux::opaque]
#[flux::refined_by(elems: Set)] //~ ERROR cannot find sort `Set`
pub struct Bar<T> {
    pub inner: std::collections::HashSet<T>,
}
