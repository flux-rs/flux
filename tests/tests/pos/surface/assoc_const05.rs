//@ignore-test: needs normalization against a known impl (step 5)

// `ThisIsOk::IS_ZST` is const-evaluable. Checking the impl's `u32[15]` against
// the trait's spec instantiated at `Self := ThisIsOk` requires normalizing
// `<ThisIsOk as TraitWithConst>::IS_ZST` to `false`, which needs `constant_info`
// to evaluate `bool` constants and the alias to reduce through the impl.

trait TraitWithConst {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32;
}

struct ThisIsOk;

impl TraitWithConst for ThisIsOk {
    const IS_ZST: bool = false;

    #[flux::spec(fn() -> u32[15])]
    fn silly_method() -> u32 {
        15
    }
}
