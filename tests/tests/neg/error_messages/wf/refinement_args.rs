#[flux::alias(type A(n: int) = i32{v: v >= n})]
type A = i32;

#[flux::sig(fn(A(false)))] //~ ERROR mismatched sorts
fn foo(x: A) {}
