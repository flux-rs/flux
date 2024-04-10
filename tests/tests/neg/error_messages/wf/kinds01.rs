#[path = "../../../lib/rset.rs"]
pub mod rset;

use std::hash::Hash;

use rset::RSet;

// This error is confusing. The problem is that `RSet` cannot be instantiated with `T` because it is
// of kind `type`. But we don't know that until after we convert the argument to `rty` and we check if
// it is a valid simple type. The reason we only know that after conv is that we need to expand type
// aliases.
#[flux::sig(fn(RSet<T>[@salt]))] //~ ERROR type cannot be refined
pub fn test01<T>(_s: RSet<T>)
where
    T: Eq + Hash,
{
}
