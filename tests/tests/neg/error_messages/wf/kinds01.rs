#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

#[flux::sig(fn(RSet<T>[@salt]))] //~ ERROR values of this type cannot be used as base sorted instances
pub fn test01<T>(_s: RSet<T>)
where
    T: Eq + Hash,
{
}
