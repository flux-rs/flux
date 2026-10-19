// Kvars without self arguments. See the test with the same name in `pos`.

pub struct S;

fn step(_s: &mut S) {}

fn toss() -> bool {
    true
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::refined_by(n: int)]
pub struct T {
    #[flux::field(i32[n])]
    pub x: i32,
}

fn consume(_t: T) {}

// No parameters, so the invariant is a kvar without arguments. The loop is reachable, so the
// invariant cannot be solved to false.
pub fn zero_args() {
    let mut s = S;
    while toss() {
        step(&mut s);
        assert(false); //~ ERROR refinement type
    }
}

// The index of `t` is in scope but `t` is moved before the loop, so the invariant is a kvar
// with one argument that is not a self argument. The loop is reachable, so the invariant cannot
// be solved to false.
#[flux::sig(fn(T{v: v > 0}))]
pub fn zero_self_args(t: T) {
    consume(t);
    let mut s = S;
    while toss() {
        step(&mut s);
        assert(false); //~ ERROR refinement type
    }
}
