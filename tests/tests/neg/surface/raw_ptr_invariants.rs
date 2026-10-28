//! Check that raw pointer bounds are not stronger than `usize` bounds.

#[flux::spec(fn(*const[@p] i32) ensures p.addr > 0)]
fn positive(_: *const i32) {} //~ ERROR refinement type

#[flux::spec(fn(*const[@p] i32) ensures p.base > 0)]
fn positive_base(_: *const i32) {} //~ ERROR refinement type

#[flux::spec(fn(*const[@p] i32) ensures p.addr + p.size < usize::MAX)]
fn below_max(_: *const i32) {} //~ ERROR refinement type
