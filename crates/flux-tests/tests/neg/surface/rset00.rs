use std::hash::Hash;
#[flux::opaque]
#[flux::refined_by(<Tiger> { elems: Set<Tiger> })]
pub struct RSet<Tiger> {
    pub inner: std::collections::HashSet<Tiger>,
}

#[flux::trusted]
#[flux::sig(fn<A as base>(s: RSet<A>) -> RSet<A>[s.elems])]
pub fn id<A>(s: RSet<A>) -> RSet<A> {
    s
}

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

#[flux::trusted]
#[flux::sig(fn() -> RSet<T>[set_empty(0)])]
pub fn empty<T>() -> RSet<T> {
    let inner = std::collections::HashSet::new();
    RSet { inner }
}

#[flux::trusted]
#[flux::sig(fn<T as base>(set: &strg RSet<T>[@s], elem: T) ensures set: RSet<T>[set_union(set_singleton(elem), s)])]
pub fn insert<T>(set: &mut RSet<T>, elem: T)
where
    T: Eq + Hash,
{
    set.inner.insert(elem);
}

#[flux::trusted]
#[flux::sig(fn<A as base>(set: &RSet<A>[@s], &A[@elem]) -> bool[set_is_in(elem, s.elems)])]
pub fn contains<A>(set: &RSet<A>, elem: &A) -> bool
where
    A: Eq + Hash,
{
    set.inner.contains(elem)
}

pub fn test() {
    let mut s = empty();
    let v0 = 666;
    let v1 = 667;
    insert(&mut s, v0);
    assert(contains(&s, &v0));
    assert(contains(&s, &v1)); //~ ERROR refinement type
}
