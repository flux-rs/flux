// Specs for `ControlFlow`, `Try for Option` and `FromResidual for Option`, which together let the
// `?` operator carry an `Option`'s `Some`/`None` discriminant across its desugaring.
extern crate flux_core;

use flux_rs::attrs::*;

// --- `ControlFlow` is refined by which arm it is ---

#[spec(fn(C) -> core::ops::ControlFlow<B, C>[true])]
fn mk_continue<B, C>(c: C) -> core::ops::ControlFlow<B, C> {
    core::ops::ControlFlow::Continue(c)
}

#[spec(fn(B) -> core::ops::ControlFlow<B, C>[false])]
fn mk_break<B, C>(b: B) -> core::ops::ControlFlow<B, C> {
    core::ops::ControlFlow::Break(b)
}

// Matching on a `ControlFlow` refines each arm.
#[spec(fn(core::ops::ControlFlow<i32, i32>[@k]) -> bool[k])]
fn is_continue(cf: core::ops::ControlFlow<i32, i32>) -> bool {
    match cf {
        core::ops::ControlFlow::Continue(_) => true,
        core::ops::ControlFlow::Break(_) => false,
    }
}

// --- `?` on `Option` ---

// The headline case: `?` on a known-`Some` cannot take the `None` path, so the function returns
// `Some`. Without the `Try`/`FromResidual` specs the discriminant is dropped here.
#[spec(fn(Option<i32>[true]) -> Option<i32>[true])]
fn qm_some(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v)
}

// Two `?`s in sequence, both known `Some`.
#[spec(fn(Option<i32>[true], Option<i32>[true]) -> Option<i32>[true])]
fn qm_two(x: Option<i32>, y: Option<i32>) -> Option<i32> {
    let a = x?;
    let b = y?;
    Some(a + b)
}

// `?` on an unknown `Option`: nothing is claimed about the result, but the body still checks.
#[spec(fn(Option<i32>) -> Option<i32>)]
fn qm_unknown(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v)
}

// The value carried through `?` keeps its refinement.
#[spec(fn(Option<i32{v: v > 0}>[true]) -> Option<i32{v: v > 0}>[true])]
fn qm_preserves_refinement(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v)
}

// A `?` that propagates `None` out of a function returning `Option`: on the break path
// `from_residual` yields `None`, so a function that can only take that path returns `None`.
#[spec(fn(Option<i32>[false]) -> Option<i32>[false])]
fn qm_none(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v)
}

// `?` interacting with the rest of the `Option` specs.
#[spec(fn(Option<i32>[true]) -> i32)]
fn qm_then_unwrap(x: Option<i32>) -> i32 {
    let y = qm_some(x);
    y.unwrap()
}

// --- `?` on `Result` ---

// A known-`Ok` cannot take the break path, so the function returns `Ok`.
#[spec(fn(Result<i32, i32>[true]) -> Result<i32, i32>[true])]
fn qm_ok(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v)
}

// A known-`Err` always breaks, so `from_residual` yields `Err`.
#[spec(fn(Result<i32, i32>[false]) -> Result<i32, i32>[false])]
fn qm_err(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v)
}

// Two `?`s in sequence, both known `Ok`.
#[spec(fn(Result<i32, i32>[true], Result<i32, i32>[true]) -> Result<i32, i32>[true])]
fn qm_ok_two(x: Result<i32, i32>, y: Result<i32, i32>) -> Result<i32, i32> {
    let a = x?;
    let b = y?;
    Ok(a + b)
}

// `?` on an unknown `Result`: nothing is claimed, but the body still checks.
#[spec(fn(Result<i32, i32>) -> Result<i32, i32>)]
fn qm_result_unknown(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v)
}

// The value carried through `?` keeps its refinement.
#[spec(fn(Result<i32{v: v > 0}, i32>[true]) -> Result<i32{v: v > 0}, i32>[true])]
fn qm_result_preserves_refinement(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v)
}

// The error-converting case: `?` bridges error types via `From`, and the `Ok`/`Err`
// discriminant still crosses intact.
struct Wrapper(i32);

impl From<i32> for Wrapper {
    #[spec(fn(i32) -> Wrapper)]
    fn from(e: i32) -> Wrapper {
        Wrapper(e)
    }
}

#[spec(fn(Result<i32, i32>[true]) -> Result<i32, Wrapper>[true])]
fn qm_converts_error(x: Result<i32, i32>) -> Result<i32, Wrapper> {
    let v = x?;
    Ok(v)
}

#[spec(fn(Result<i32, i32>[false]) -> Result<i32, Wrapper>[false])]
fn qm_converts_error_err(x: Result<i32, i32>) -> Result<i32, Wrapper> {
    let v = x?;
    Ok(v)
}

#[spec(fn (n: usize) -> Option<usize[n-1]>[n > 0])]
fn decr(n: usize) -> Option<usize> {
    if n > 0 { Some(n - 1) } else { None }
}

#[spec(fn (n: usize) -> Option<usize[n-2]>[n > 1])]
fn test_decr(n: usize) -> Option<usize> {
    let n = decr(n)?;
    let n = decr(n)?;
    Some(n)
}
