// Test that we don't fail when normalizing an associated refinement on a dynamic object

#[flux::assoc(fn blueberry_assoc(x: int) -> bool)]
pub trait MyTrait {
    #[flux::sig(fn(&Self) -> i32{v: Self::blueberry_assoc(v) })]
    fn blueberry(&self) -> i32;
}

fn foo(s: &dyn MyTrait) {
    s.blueberry();
}
