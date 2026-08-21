// A trait declaration on its own. `Self::IS_ZST` must resolve through the
// `SelfTyParam` bound (step 1) and be assigned sort `bool` without demanding a
// value (step 2). There is no impl and no body, so nothing beyond conversion
// runs.

trait TraitWithConst {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn silly_method() -> u32;
}
