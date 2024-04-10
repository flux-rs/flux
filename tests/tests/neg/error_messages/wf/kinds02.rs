#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

fn mk_eq_hash() -> impl Eq + Hash {
    0
}

#[flux::sig(fn<T as base>(x:T) -> T[x])]
fn id<T>(x: T) -> T {
    x
}

// This will try to call id  with an `RSet<impl Eq + Hash>` which can't be a "base"
pub fn test00() {
    let z = mk_eq_hash();
    id(z); //~ ERROR cannot instantiate
}

// This will try to create an `RSet<impl Eq + Hash>` which can't be put into RSet
pub fn test01() {
    let x = mk_eq_hash();
    let mut s = RSet::new(); //~ ERROR cannot instantiate
    s.insert(x);
}

// #[flux::sig(fn<T as base>(x:T))]
// pub fn test01<T>(x: T) {
//     id(x); // TODO: REJECT-but-actually-ok
// }

// fn test_bob<T>(x: T) {
//     let z = mk_eq_hash();
//     bob(z); // TODO: REJECT-but-actually-ok
// }
