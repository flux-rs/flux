// Soundness counterpart to `pos/fold_unfold/unblock_shared_borrow.rs`.
//
// Same shared-borrow + fold shape that used to ICE, but with a postcondition
// that does NOT hold: `g` claims to return `n + 1` while it returns `s.a == n`.
// Dropping the (no-op) `Unblock` for the shared borrow must not weaken the
// checker: it still knows `s.a == n` across the borrow/fold and rejects the
// bogus postcondition.

#[flux::refined_by(a: int)]
struct S {
    #[flux::field(u64[a])]
    a: u64,
    b: String,
}

fn f(s: &S, t: &str) {}

#[flux::sig(fn(s: S[@n]) -> u64[n + 1])]
fn g(s: S) -> u64 {
    let t = &s.b; // shared borrow of the non-Copy field `b`
    f(&s, t); // also borrows `&s`, forcing `s` to be folded
    s.a //~ ERROR refinement type
}
