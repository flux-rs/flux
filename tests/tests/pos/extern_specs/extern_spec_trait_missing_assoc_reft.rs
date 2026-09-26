// An extern spec can add an associated refinement without a default body to a trait. Existing
// implementations in other crates don't define it, so for them it is treated as uninterpreted.

use flux_attrs::*;

#[extern_spec(std::clone)]
#[assoc(fn eval(x: int) -> int)]
trait Clone {}

#[trusted]
#[sig(fn(x: i32) -> i32[<T as Clone>::eval(x)])]
fn test01<T: Clone>(x: i32) -> i32 {
    x
}

// `String: Clone` is implemented in `alloc`, so `<String as Clone>::eval` is uninterpreted, but we
// can still reason about it by congruence.
#[sig(fn() -> bool[true])]
pub fn test_string() -> bool {
    test01::<String>(0) == test01::<String>(0)
}
