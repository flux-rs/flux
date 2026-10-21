//! Check that raw pointer bounds are assumed, independently of the overflow mode.

#![flux::opts(check_overflow = "none")]

#[flux::spec(fn(*const[@p] i32) ensures p.base >= 0 && p.addr >= 0)]
fn lower(_: *const i32) {}

#[flux::spec(fn(*const[@p] i32) ensures p.addr <= usize::MAX && p.addr + p.size <= usize::MAX)]
fn upper(_: *const i32) {}

#[flux::spec(fn(*const[@p] i32) ensures p.addr != 0 => p.addr > 0)]
fn non_null_is_positive(_: *const i32) {}
