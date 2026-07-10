// Regression test for an ICE in the `unblock` ghost statement.
//
// A shared borrow of a non-`Copy` field (`&s.b`) kept live across a call that
// also borrows the whole struct (`&s`) used to crash: passing `&s` forced `s`
// to be folded back to an `Indexed(Adt(S))`, and the (spurious) `Unblock(s.b)`
// emitted for the shared borrow tried to walk a `Field` projection into the
// folded ADT, hitting `tracked_span_bug!` in `PlacesTree::unblock`.
//
// The fix only emits `Unblock` for mutable borrows (the only ones that ever
// block a place). This test additionally checks soundness: the refinement on
// `s.a` must still be tracked across the borrow/fold, so `g` provably returns
// `n`.

#[flux::refined_by(a: int)]
struct S {
    #[flux::field(u64[a])]
    a: u64,
    b: String,
}

fn f(s: &S, t: &str) {}

#[flux::sig(fn(s: S[@n]) -> u64[n])]
fn g(s: S) -> u64 {
    let t = &s.b; // shared borrow of the non-Copy field `b`
    f(&s, t); // also borrows `&s`, forcing `s` to be folded
    s.a // `s.a == n` must survive the borrow/fold
}
