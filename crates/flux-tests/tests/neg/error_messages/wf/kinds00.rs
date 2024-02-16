#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

pub fn test00_ok() -> Option<impl Eq + Hash> {
    Some(1)
}

pub fn test00_bad() -> RSet<impl Eq + Hash> {
    //~^ ERROR values of this type cannot be used as base sorted instances
    RSet::<i32>::new()
}

#[flux::sig(fn(soup:RSet<Tinker>))] //~ ERROR values of this type cannot be used as base sorted instances
pub fn test01<Tinker: Eq + Hash>(_s: RSet<Tinker>) {}
