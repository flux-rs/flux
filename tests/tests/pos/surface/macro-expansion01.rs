// test that we correctly check specs expanded from a macro that is instantiated
// at several different types
use flux_attrs::*;

macro_rules! make_id {
    ($name:ident, $ty:ty) => {
        #[spec(fn(x: $ty) -> $ty[x])]
        pub fn $name(x: $ty) -> $ty {
            x
        }
    };
}

make_id!(id_i32, i32);
make_id!(id_usize, usize);

#[spec(fn() -> i32[1])]
pub fn test_i32() -> i32 {
    id_i32(1)
}

#[spec(fn(n: usize) -> usize[n])]
pub fn test_usize(n: usize) -> usize {
    id_usize(n)
}
