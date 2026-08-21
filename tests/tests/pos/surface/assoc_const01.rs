// Split into smaller staged tests in assoc_const02.rs .. assoc_const06.rs.

trait TraitWithConst {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32;
}

struct Thingy<T>(T);

impl<T> TraitWithConst for Thingy<T> {
    const IS_ZST: bool = size_of::<T>() == 0;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32 {
        if Self::IS_ZST { 0 } else { 100 }
    }
}

struct ThisIsOk;

impl TraitWithConst for ThisIsOk {
    const IS_ZST: bool = false;

    #[flux::spec(fn() -> u32[15])]
    fn silly_method() -> u32 {
        15
    }
}
