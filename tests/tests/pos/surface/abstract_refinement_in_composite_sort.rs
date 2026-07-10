#[flux::refined_by(len: int, hrn pred: int -> bool)]
struct Inner {
    #[flux::field(i32[len])]
    len: i32,
    #[flux::field(i32{v: pred(v)})]
    witness: i32,
}

#[flux::refined_by(inner: Inner, tag: int)]
struct Outer {
    #[flux::field(Inner[inner])]
    inner: Inner,
    #[flux::field(i32[tag])]
    tag: i32,
}

#[flux::sig(fn() -> Inner[0, |i| i >= 0])]
fn direct() -> Inner {
    Inner { len: 0, witness: 0 }
}

#[flux::sig(fn() -> Outer[Inner { len: 0, pred: |i| i >= 0 }, 0])]
fn nested() -> Outer {
    Outer { inner: direct(), tag: 0 }
}

#[flux::sig(fn(Outer[Inner { len: 0, pred: |i| i >= 0 }, 0]))]
fn check(_: Outer) {}

fn test() {
    check(nested());
    let _ = direct();
}
