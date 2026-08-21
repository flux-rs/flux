//@ignore-test: needs the MIR constant tied to the same symbol (step 4)

// The body branches on `Self::IS_ZST`. In MIR that is
// `switchInt(const <Thingy<T> as TraitWithConst>::IS_ZST)`, an unevaluated
// const that cannot be evaluated because it depends on `T`. It must be given
// the same logical symbol as the `Self::IS_ZST` in the spec, otherwise the
// then-branch cannot prove `v == 0`.

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
