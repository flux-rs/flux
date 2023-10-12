use std::hash::Hash;
#[flux::opaque]
#[flux::refined_by(elems: Set<T>)]
pub struct RSet<T> {
    inner: std::collections::HashSet<T>,
}

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn empty<T>() -> RSet<T> {
    RSet { inner: std::collections::HashSet::new() }
}

#[flux::trusted]
#[flux::sig(fn(set: &strg RSet[@s], elem: T) ensures set: RSet[ set_union(set_singleton(x), s) ])]
pub fn insert<T>(set: &mut RSet<T>, elem: T)
where
    T: Eq + Hash,
{
    set.inner.insert(elem);
}

#[flux::trusted]
#[flux::sig(fn(set: &Set<T>[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
pub fn contains<T>(set: &RSet<T>, elem: &T) -> bool
where
    T: Eq + Hash,
{
    set.inner.contains(elem)
}

pub fn test() {
    let mut s = empty();
    insert(&mut s, 1);
    assert(contains(&s, &1));
    assert(!contains(&s, &2));
}
