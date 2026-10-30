//@compile-flags: -Fdump-vc-skeleton

#[flux::sig(fn(x: i32) -> i32[x + 1])]
fn successor(x: i32) -> i32 { x + 1 }

#[flux::sig(fn(x: i32, i32[x + 1]) -> i32[x])]
fn related(x: i32, _: i32) -> i32 { x }

#[flux::sig(fn(x: i32) ensures x == x)]
fn postcondition(_: i32) {}

#[flux::sig(fn(x: i32) requires (forall i in 0 .. 4 { i + x >= x }))]
fn quantified(_: i32) {}

#[flux::sig(fn(x: i32) -> i32[x + 2])]
fn caller(x: i32) -> i32 {
    successor(successor(x))
}

#[flux::refined_by(n: int)]
struct Bag<T> {
    #[flux::field(usize[n])]
    len: usize,
    value: T,
}

// Nontrivial predicates inside generic arguments must survive marker erasure.
#[flux::sig(fn(Bag<Bag<i32>[10]>))]
fn nested(_: Bag<Bag<i32>>) {}

// Both explicit and lifted signatures must place post-mutation markers.
#[flux::sig(fn(&mut Bag<i32>))]
fn mutable(_: &mut Bag<i32>) {}

fn lifted(_: &mut Bag<i32>) {}

#[flux::sig(fn(&mut Bag<i32>))]
fn mutable_caller(x: &mut Bag<i32>) {
    mutable(x);
    lifted(x);
}
