#![flux::defs {
    fn gtzero(x: int) -> bool {
        x > 0
    }
}]

// Test that defn can be used inside invariant
#[flux::refined_by(n: int)]
#[flux::invariant(gtzero(n))]
struct S {
    #[flux::field({i32[@n] | gtzero(n)})]
    x: i32,
}

#[flux::sig(fn(S[@n]) -> i32{v: v > 0})]
fn test(s: S) -> i32 {
    s.x
}
