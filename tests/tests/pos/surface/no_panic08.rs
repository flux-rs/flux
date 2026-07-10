// Regression: the *same* generic function instantiated at two different impls must be resolved
// independently per mono instance. `dispatch::<S>` (identity) is `MightPanic` (unresolved trait
// call), but both `dispatch::<Square>` and `dispatch::<Circle>` resolve to non-panicking methods,
// so a single `#[flux::no_panic]` caller that uses both instantiations is accepted. This exercises
// the instance-keyed spec map distinguishing two monos that share one `DefId`.

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

struct Circle {
    r: usize,
}

impl Shape for Circle {
    fn area(&self) -> usize {
        3 * self.r * self.r
    }
}

fn dispatch<S: Shape>(s: &S) -> usize {
    s.area()
}

// A second layer of generality: `dispatch_twice::<S>` is itself only `MightPanic` as the identity
// instance, but each mono instance is `WillNotPanic` once `dispatch::<S>` resolves.
fn dispatch_twice<S: Shape>(a: &S, b: &S) -> usize {
    dispatch(a) + dispatch(b)
}

#[flux::no_panic]
fn caller() -> usize {
    let sq = dispatch(&Square { side: 3 });
    let ci = dispatch(&Circle { r: 2 });
    let tw = dispatch_twice(&Square { side: 1 }, &Square { side: 2 });
    sq + ci + tw
}
