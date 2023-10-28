#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

/// TODO: Crashes, but should ACCEPT; passes in `main` but BREAKS in `rset` branch;
/// so should allow it in `rset`
pub fn test00_ok() -> Option<impl Eq + Hash> {
    Some(1)
}

pub fn test00_bad() -> RSet<impl Eq + Hash> {
    //~^ ERROR values of this type cannot be used as base sorted instances
    RSet::<i32>::new()
}

fn mk_eq_hash() -> impl Eq + Hash {
    0
}

/*
#[flux::sig(fn<T as base>(x:T) -> T[x])]
fn id<T>(x: T) -> T {
    x
}

pub fn test_base() {
    let z = mk_eq_hash();
    id(z);
}
/// TODO: This currently crashes. We should gracefully reject it.
///     x: impl Eq + Hash
/// This will try to create an `RSet<impl Eq + Hash>` which can't be put into RSet
fn test02() {
    let x = mk_eq_hash();
    let mut s = RSet::new();
    s.insert(x);
}

/// TODO: currently accept but should REJECT gracefully as `RSet<T>` is
/// not well-formed if `T` is of kind type (i.e. not marked `base`).
#[flux::sig(fn(RSet<T>[@s]))]
fn test04<T: Eq + Hash>(set: RSet<T>) {}

/// TODO: variant of `test04` above should be rejected, as `RSet<T>[@s]` is
/// not well-formed unless `T` is marked as 'special'.
#[flux::sig(fn(RSet<T>[@s]))]
pub fn test05<T>(s: RSet<T>)
where
    T: Eq + Hash,
{
}

#[flux::sig(fn<T as base>(x: T))]
fn foo<T>(x: T) {}

/// TODO: Fails with parameter inference call but should fail with kind error.
fn test06() {
    let x = mk_eq_hash();
    foo(x);
}



*/
