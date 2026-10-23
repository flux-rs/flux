// Kvars without self arguments. The invariant of each loop below is a kvar whose self arguments
// are the indices of the locals at the loop head. All those locals are unit sorted, so the kvar
// has no self arguments, and at most the indices of the parameters in scope as arguments.

pub struct S;

fn step(_s: &mut S) {}

fn toss() -> bool {
    true
}

#[flux::sig(fn() -> i32{v: v > 0})]
fn positive() -> i32 {
    1
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::refined_by(n: int)]
pub struct T {
    #[flux::field(i32[n])]
    pub x: i32,
}

fn consume(_t: T) {}

// No parameters, so the invariant is a kvar without arguments.
pub fn zero_args() {
    let mut s = S;
    while toss() {
        step(&mut s);
        assert(positive() >= 0);
    }
}

// The index of `t` is in scope but `t` is moved before the loop, so the invariant is a kvar
// with one argument that is not a self argument.
#[flux::sig(fn(T{v: v > 0}))]
pub fn zero_self_args(t: T) {
    consume(t);
    let mut s = S;
    while toss() {
        step(&mut s);
        assert(positive() >= 0);
    }
}

// Same, but the precondition is contradictory, so the invariant must be solved to false.
#[flux::sig(fn(T{v: v > 0 && v < 0}))]
pub fn zero_self_args_dead(t: T) {
    consume(t);
    let mut s = S;
    while toss() {
        step(&mut s);
        assert(false);
    }
}
