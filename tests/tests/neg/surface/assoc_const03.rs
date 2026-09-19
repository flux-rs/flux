// The body reads `Self::IS_ZST` and so is checked against the same symbol the
// spec uses. Returning `1` in the branch where the spec promises `v == 0` must
// be rejected: a pass here would mean the branch condition carries no
// information.

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
        if Self::IS_ZST { 1 } else { 100 } //~ ERROR refinement type
    }
}
