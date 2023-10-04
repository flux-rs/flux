#[flux::refined_by(a: int, b: int)]
#[flux::invariant(a > 0)]
#[flux::invariant(b > 0)] //~ ERROR invariant
pub struct S {
    #[flux::field({i32[@a] | a > 0})]
    fst: i32,
    #[flux::field({i32[@b] | a >= b})]
    snd: i32,
}
