#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

// this is OK because we just dont generate an index for `soup`
#[flux::sig(fn(soup:RSet<Tinker>))]
pub fn test04<Tinker: Eq + Hash>(_s: RSet<Tinker>) {}

#[flux::sig(fn(RSet<T>[@salt]))] //~ ERROR type cannot be refined
pub fn test05<T>(_s: RSet<T>)
where
    T: Eq + Hash,
{
}
