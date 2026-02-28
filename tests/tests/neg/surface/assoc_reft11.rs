// Test that we don't fail when normalizing an associated refinement on a dynamic object

#[flux::assoc(fn blueberry_assoc(x: int) -> bool)]
pub trait MyTrait {
    #[flux::sig(fn(&Self, x: i32{Self::blueberry_assoc(x)}))]
    fn blueberry(&self, x: i32);
}

fn foo(s: &dyn MyTrait) {
    s.blueberry(0); //~ ERROR refinement type error
}
