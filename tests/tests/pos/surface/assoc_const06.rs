//@ignore-test: needs normalization to fall back to a trait default (step 5)

// `Inherit` does not define `IS_ZST`, so there is no impl item to look up and
// normalization has to fall back to the trait's own default body. Confirmed
// against rustc: MIR still reports `def` as the *trait* item here, exactly as
// it does when an impl overrides the default.

trait TraitWithConst {
    const IS_ZST: bool = false;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32;
}

struct Inherit;

impl TraitWithConst for Inherit {
    #[flux::spec(fn() -> u32[15])]
    fn silly_method() -> u32 {
        15
    }
}
