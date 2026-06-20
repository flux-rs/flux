// Regression: the instance-keying win, exercised purely by the no-panic *inference* (no flux specs,
// no deps, no refinements) on a generic function that calls into the standard library through an
// iterator.
//
// `drain<I: Iterator>` calls `it.next()`. As the *identity* instance `drain::<I>` this is an
// unresolved `<I as Iterator>::next` trait call, so its inferred spec is `MightPanic` — a `DefId`-
// keyed spec map (the pre-change behavior) would stop here and reject the caller. Only the *mono*
// instance `drain::<Empty<i32>>` resolves the call to the concrete standard-library instance
// `<core::iter::Empty<i32> as Iterator>::next`, whose monomorphized MIR returns `None` with no
// panic edges and is `WillNotPanic`. The `#[flux::no_panic]` caller is accepted only because the
// checker queries that mono std instance at the call site.

fn drain<I: Iterator<Item = i32>>(mut it: I) -> Option<i32> {
    it.next()
}

#[flux::no_panic]
fn drain_empty() -> Option<i32> {
    drain(core::iter::empty::<i32>())
}

// A direct call into a generic standard-library function: `core::iter::empty::<i32>` and the
// monomorphized `Empty::<i32>::next` are both panic-free, so the inference proves this no-panic
// without any instantiation in our own code.
#[flux::no_panic]
fn empty_next() -> Option<i32> {
    let mut it = core::iter::empty::<i32>();
    it.next()
}
