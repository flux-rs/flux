pub trait Silly<A> {
    #[flux::sig(fn(&Self, z: A) -> i32{v:100 < v})]
    fn bloop(&self, z: A) -> i32;
}

impl Silly<bool> for i32 {
    #[flux::sig(fn(&Self, b : bool) -> i32[2000])]
    fn bloop(&self, _b: bool) -> i32 {
        2000
    }
}

#[flux::sig(fn(i32) -> i32{v: 100 < v})]
pub fn client(x: i32) -> i32 {
    let y = x.bloop(true);
    y + 1
}

#[flux::sig(fn(_, _) -> i32{v:100 < v})]
pub fn client2<A, B: Silly<A>>(x: B, y: A) -> i32 {
    x.bloop(y)
}
