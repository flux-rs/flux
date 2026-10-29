//@compile-flags: -Fdump-vc-skeleton

#[flux::sig(fn(x: i32) -> i32[x + 1])]
fn successor(x: i32) -> i32 { x + 1 }

#[flux::sig(fn(x: i32, i32[x + 1]) -> i32[x])]
fn related(x: i32, _: i32) -> i32 { x }

#[flux::sig(fn(x: i32) ensures x == x)]
fn postcondition(_: i32) {}

#[flux::sig(fn(x: i32) requires (forall i in 0 .. 4 { i + x >= x }))]
fn quantified(_: i32) {}
