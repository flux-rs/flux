// Step 1: A trait declaration on its own. `Self::IS_ZST` must resolve through the
// `SelfTyParam` bound and be assigned sort `bool` sans actual value.

trait TraitWithConst {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32;
}

// Step 2: The impl's spec is checked against the trait's spec instantiated at
// `Self := Thingy<T>`. Both mention `Self::IS_ZST` and must keep denoting the
// same "uninterpreted symbol" (no knowledge of the const's value is needed here.)
// However, the body branches on `Self::IS_ZST` or in MIR
// `switchInt(const <Thingy<T> as TraitWithConst>::IS_ZST)`, an unevaluated
// const that cannot be evaluated because it depends on `T`, we have to link
// that with the same logical symbol as the `Self::IS_ZST` in the spec.

struct Thingy<T>(T);

impl<T> TraitWithConst for Thingy<T> {
    const IS_ZST: bool = size_of::<T>() == 0;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32 {
        if Self::IS_ZST { 0 } else { 100 }
    }
}

// Step 3: `ThisIsOk::IS_ZST` is const-evaluable. Checking the impl's `u32[15]` against
// the trait's spec instantiated at `Self := ThisIsOk` which requires normalizing
// `<ThisIsOk as TraitWithConst>::IS_ZST` to `false`

struct ThisIsOk;

impl TraitWithConst for ThisIsOk {
    const IS_ZST: bool = false;

    #[flux::spec(fn() -> u32[15])]
    fn silly_method() -> u32 {
        15
    }
}

// Step 4: Allow constant annotations on associated constants (which might mention
// generics, and other associated refinements...)

struct Blingy<T>(T);

#[flux::trusted(reason = "extern-spec")]
#[flux::spec(fn() -> bool[T::size_of() == 0])]
fn fake_size_of<T>() -> bool {
    size_of::<T>() == 0
}

impl<T> TraitWithConst for Blingy<T> {
    #[flux::constant(T::size_of() == 0)]
    const IS_ZST: bool = size_of::<T>() == 0;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32 {
        let is_zst = fake_size_of::<T>();
        if is_zst { 0 } else { 100 }
    }
}

// Step 5: Resolve const values from trait if not supplied in impl;
// `Inherit` does not define `IS_ZST`, so there is no impl item to
// look up and normalization has to fall back to the trait's own
// default body.

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
