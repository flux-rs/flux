#[derive(Clone, Copy)]
#[flux::opaque]
#[flux::refined_by(p: int -> bool)]
pub struct S;

#[flux::sig(fn(S[|x| x > 0]) -> bool[true])]
pub fn test00(x: S) -> bool {
    #[flux::sig(fn(x: S) -> bool[set_is_in(x.p, set_singleton(x.p))])]
    pub fn f(_: S) -> bool {
        true
    }
    f(x)
}

#[flux::sig(fn(S[|x| x > 0]))]
fn test01(x: S) {
    #[flux::sig(fn<T as base>(x: T, y: T{y == x}))]
    fn f<T>(x: T, y: T) {}

    f(x, x);
}
