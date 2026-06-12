// Regression (negative): instance-keying must not over-approve. The generic `dispatch<S: Shape>`
// is resolved per mono instance, so two instantiations in the *same* `#[flux::no_panic]` caller are
// classified independently: `dispatch::<Square>` is `WillNotPanic` (accepted), but
// `dispatch::<Spiky>` resolves `s.area()` to a method that may panic (unguarded array index), so it
// is `MightPanic` and the call must be rejected. A bug that keyed only by `DefId`, or that trusted
// the identity instance, would either reject both or accept both.
//
// `Spiky::area` is made may-panic by calling into a helper that may panic (the `println!` path),
// *not* by an array index: an unguarded index would additionally raise an unrelated Flux
// bounds-check refinement error, which would mask the no-panic diagnostic under test.

trait Shape {
    fn area(&self) -> usize;
}

struct Square {
    side: usize,
}

impl Shape for Square {
    fn area(&self) -> usize {
        self.side
    }
}

struct Spiky {
    n: usize,
}

impl Shape for Spiky {
    fn area(&self) -> usize {
        noisy(); // calls into a may-panic helper
        self.n
    }
}

// Not `no_panic`: reaches `println!`, which the no-panic inference classifies as `MightPanic`.
fn noisy() {
    println!("spiky");
}

fn dispatch<S: Shape>(s: &S) -> usize {
    s.area()
}

#[flux::no_panic]
fn caller() -> usize {
    let ok = dispatch(&Square { side: 3 });
    let bad = dispatch(&Spiky { n: 5 }); //~ ERROR may panic
    ok + bad
}
