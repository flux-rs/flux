#[flux::refined_by(f: int -> bool)]
#[flux::opaque]
struct Inner;

#[flux::refined_by(inner: Inner, tag: int)]
#[flux::opaque]
struct Outer;

#[flux::sig(fn(&Inner[@f]) -> bool[f(0)])]
#[flux::trusted]
fn direct(_: &Inner) -> bool {
    true
}

#[flux::sig(fn(&Outer[@s]) -> bool[s.inner.f(0)])]
#[flux::trusted]
fn nested(_: &Outer) -> bool {
    true
}
