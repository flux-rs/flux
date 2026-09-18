// test that we correctly check specs expanded from a macro that is instantiated
// at several different types
use flux_attrs::*;

macro_rules! make_id {
    ($name:ident, $ty:ty) => {
        #[spec(fn(x: $ty) -> $ty[x])]
        pub fn $name(x: $ty) -> $ty {
            x + 1 //~ ERROR: refinement type
        }
    };
}

make_id!(id_i32, i32);
