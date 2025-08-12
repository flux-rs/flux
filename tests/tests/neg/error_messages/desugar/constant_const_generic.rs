use flux_rs::attrs::*;

const C: usize = 0;

struct S<const N: usize> {}

#[spec(fn(S<C>))] //~ ERROR `constant` not supported in this position
fn foo(x: S<C>) {}
