// The impl's spec is checked against the trait's spec instantiated at
// `Self := Thingy<T>`. Both mention `Self::IS_ZST` and must keep denoting the
// same symbol once `ConstDefId` carries generic arguments.
//
// The body returns a constant satisfying both branches, so no knowledge of the
// const's value is needed here (that is assoc_const04.rs). Note this test does
// not by itself distinguish a correct instantiation from one that conflates all
// instantiations into a single symbol -- see neg/surface/assoc_const02.rs.

trait TraitWithConst {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { 0 < v } else { 10 < v }})]
    fn silly_method() -> u32;
}

struct Thingy<T>(T);

impl<T> TraitWithConst for Thingy<T> {
    const IS_ZST: bool = size_of::<T>() == 0;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { 0 < v } else { 10 < v }})]
    fn silly_method() -> u32 {
        100
    }
}
