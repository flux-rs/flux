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

// // this is OK because we just dont generate an index for `soup`
// #[flux::sig(fn(soup:RSet<Tinker>))]
// pub fn test04<Tinker: Eq + Hash>(_s: RSet<Tinker>) {}

#[flux::sig(fn(RSet<T>[@salt]))] //~ ERROR type cannot be refined
pub fn test05<T>(s: RSet<T>)
where
    T: Eq + Hash,
{
}
