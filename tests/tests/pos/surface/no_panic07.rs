// Regression: the no-panic call graph must substitute a generic function's concrete type args
// before resolving the callees in its body (the `instantiate_mir_and_normalize_erasing_regions`
// call in `flux-opt`'s `callees_in_body`), and the inferred specs must be keyed by `Instance` so
// the checker can recover the *mono* spec at the call site.
//
// As the identity instance `dispatch::<S>`, the call `s.area()` is an unresolved trait call, so its
// inferred spec is `MightPanic`. Only the mono instance `dispatch::<Square>` resolves it to the
// concrete, non-panicking `<Square as Shape>::area`. The `#[flux::no_panic]` caller below is
// accepted only because the checker queries that mono instance (location -> instance -> spec),
// rather than the pessimistic identity instance.

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

// Not marked `no_panic`: the identity instance is `MightPanic` (unresolved trait call). Only the
// mono instance `dispatch::<Square>` is `WillNotPanic`.
fn dispatch<S: Shape>(s: &S) -> usize {
    s.area()
}

#[flux::no_panic]
fn caller() -> usize {
    dispatch(&Square { side: 3 })
}
