// Regression test for #1786: an implemented associated refinement with an incompatible sort must
// be reported instead of being used to normalize the trait's associated refinement.

#[flux::assoc(fn p(x: Self) -> bool)]
pub trait MyTrait {
    #[flux::sig(fn(Self[@x]) -> bool[Self::p(x)])]
    fn method(self) -> bool;
}

// The index of a reference has sort `()`, so `p` should take a `()` not an `int`
#[flux::assoc(fn p(n: int) -> bool { n == 0 })] //~ ERROR implemented associated refinement `p` has an incompatible sort for trait
impl MyTrait for &u8 {
    #[flux::sig(fn(&u8) -> bool[true])]
    fn method(self) -> bool {
        true
    }
}
