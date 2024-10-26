pub trait Silly<A> {
    #[flux::sig(fn(&Self, z: A) -> i32{v:100 < v})]
    fn bloop(&self, z: A) -> i32;
}

impl Silly<bool> for i32 {
    #[flux::sig(fn(&Self, b : bool) -> i32[20])]
    fn bloop(&self, _b: bool) -> i32 {
        //~^ ERROR refinement type
        20
    }
}
