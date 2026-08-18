// Negative counterparts to `pos/extern_specs/control_flow00.rs`: the `ControlFlow` arm and the
// discriminant carried across `?` are tracked precisely, so claiming the wrong one is rejected.
extern crate flux_core;

use flux_rs::attrs::*;

// --- `ControlFlow` arms are not interchangeable ---

#[spec(fn(C) -> core::ops::ControlFlow<B, C>[false])]
fn continue_is_not_break<B, C>(c: C) -> core::ops::ControlFlow<B, C> {
    core::ops::ControlFlow::Continue(c)
} //~ ERROR refinement type error

#[spec(fn(B) -> core::ops::ControlFlow<B, C>[true])]
fn break_is_not_continue<B, C>(b: B) -> core::ops::ControlFlow<B, C> {
    core::ops::ControlFlow::Break(b)
} //~ ERROR refinement type error

// Matching refines each arm, so the arms cannot be swapped.
#[spec(fn(core::ops::ControlFlow<i32, i32>[@k]) -> bool[k])]
fn is_continue_swapped(cf: core::ops::ControlFlow<i32, i32>) -> bool {
    match cf {
        core::ops::ControlFlow::Continue(_) => false, //~ ERROR refinement type error
        core::ops::ControlFlow::Break(_) => true, //~ ERROR refinement type error
    }
}

// --- `?` on `Option` ---

// `?` on a known-`None` always takes the break path, so the result is `None`, not `Some`.
#[spec(fn(Option<i32>[false]) -> Option<i32>[true])]
fn qm_none_is_not_some(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v)
} //~ ERROR refinement type error

// `?` on an unknown `Option` may take the break path, so `Some` cannot be claimed.
#[spec(fn(Option<i32>) -> Option<i32>[true])]
fn qm_unknown_is_not_some(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v)
} //~ ERROR refinement type error

// Symmetrically, a known-`Some` input cannot yield `None`.
#[spec(fn(Option<i32>[true]) -> Option<i32>[false])]
fn qm_some_is_not_none(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v) //~ ERROR refinement type error
}

// `?` carries the value's refinement through unchanged; it does not strengthen it.
#[spec(fn(Option<i32{v: v > 0}>[true]) -> Option<i32{v: v > 10}>[true])]
fn qm_does_not_strengthen(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v) //~ ERROR refinement type error
}

// --- `?` on `Result` ---

// `?` on a known-`Err` always breaks, so the result is `Err`, not `Ok`.
#[spec(fn(Result<i32, i32>[false]) -> Result<i32, i32>[true])]
fn qm_err_is_not_ok(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v)
} //~ ERROR refinement type error

// `?` on an unknown `Result` may break, so `Ok` cannot be claimed.
#[spec(fn(Result<i32, i32>) -> Result<i32, i32>[true])]
fn qm_result_unknown_is_not_ok(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v)
} //~ ERROR refinement type error

// Symmetrically, a known-`Ok` input cannot yield `Err`.
#[spec(fn(Result<i32, i32>[true]) -> Result<i32, i32>[false])]
fn qm_ok_is_not_err(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v) //~ ERROR refinement type error
}

// `?` carries the value's refinement through unchanged; it does not strengthen it.
#[spec(fn(Result<i32{v: v > 0}, i32>[true]) -> Result<i32{v: v > 10}, i32>[true])]
fn qm_result_does_not_strengthen(x: Result<i32, i32>) -> Result<i32, i32> {
    let v = x?;
    Ok(v) //~ ERROR refinement type error
}

// The discriminant is tracked across the `From` error conversion too.
struct Wrapper(i32);

impl From<i32> for Wrapper {
    #[spec(fn(i32) -> Wrapper)]
    fn from(e: i32) -> Wrapper {
        Wrapper(e)
    }
}

#[spec(fn(Result<i32, i32>[false]) -> Result<i32, Wrapper>[true])]
fn qm_converts_error_wrong_arm(x: Result<i32, i32>) -> Result<i32, Wrapper> {
    let v = x?;
    Ok(v)
} //~ ERROR refinement type error
