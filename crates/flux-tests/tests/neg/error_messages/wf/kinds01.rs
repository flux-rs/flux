#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

#[flux::sig(fn(soup:RSet<Tinker>))] //~ ERROR values of this type cannot be used as base sorted instances
pub fn test04<Tinker: Eq + Hash>(_s: RSet<Tinker>) {}

#[flux::sig(fn(RSet<T>[@salt]))] //~ ERROR type cannot be refined
pub fn test05<T>(_s: RSet<T>)
where
    T: Eq + Hash,
{
}
