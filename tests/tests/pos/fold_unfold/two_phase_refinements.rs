#[flux::refined_by(exp: int)]
struct S {
    #[flux::field(i32[exp])]
    exp: i32,
}

impl S {
    #[flux::sig(fn(&mut S, i32{v: v > 0}))]
    fn positive(&mut self, _value: i32) {}
}

#[flux::sig(fn(S[1]))]
fn argument_refinement(mut b: S) {
    b.positive(b.exp);
    b.exp = 0;
}
