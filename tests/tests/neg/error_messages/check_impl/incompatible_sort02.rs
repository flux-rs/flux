// Regression test for #1786: the error must be reported even if a use site that normalizes the
// associated refinement is checked before the implementation.

#[flux::assoc(fn p(x: Self) -> bool)]
pub trait MyTrait {
    #[flux::sig(fn(Self[@x]) -> bool[Self::p(x)])]
    fn method(self) -> bool;
}

pub fn test(x: &u8) -> bool {
    x.method()
}

#[flux::assoc(fn p(n: int) -> bool { n == 0 })] //~ ERROR implemented associated refinement `p` has an incompatible sort for trait
impl MyTrait for &u8 {
    #[flux::sig(fn(&u8) -> bool[true])]
    fn method(self) -> bool {
        true
    }
}
