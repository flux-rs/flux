#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

fn mk_eq_hash() -> impl Eq + Hash {
    0
}

#[flux::sig(fn<T as base>(x:T) -> T[x])]
fn id<T>(x: T) {}

pub fn test_base() {
    let z = mk_eq_hash(); // TODO: REJECT
    id(z);
}

fn bob(x: T) {
    id(x) // TODO: REJECT-but-actually-ok
}

fn test_bob(x: T) {
    let z = mk_eq_hash();
    bob(z) // TODO: REJECT-but-actually-ok
}

/// TODO: This currently crashes. We should gracefully reject it.
///     x: impl Eq + Hash
/// This will try to create an `RSet<impl Eq + Hash>` which can't be put into RSet
fn test02() {
    let x = mk_eq_hash();
    let mut s = RSet::new();
    s.insert(x);
}
