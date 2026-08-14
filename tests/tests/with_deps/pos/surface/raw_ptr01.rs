use flux_attrs::*;

#[flux::spec(fn(*const[@p] i32))]
pub fn const_single(_ptr: *const i32) {}

#[flux::spec(fn(*mut[@p] i32))]
pub fn mut_single(_ptr: *mut i32) {}

#[flux::spec(fn(*const[@base, @addr, @size] i32))]
pub fn const_parts(_ptr: *const i32) {}

#[flux::spec(fn(*mut[@base, @addr, @size] i32))]
pub fn mut_parts(_ptr: *mut i32) {}

#[flux::spec(fn({*const[@base, @addr, @size] i32 | size > 0}))]
pub fn const_parts_constrained(_ptr: *const i32) {}

#[flux::spec(fn({*mut[@base, @addr, @size] i32 | size > 0}))]
pub fn mut_parts_constrained(_ptr: *mut i32) {}

#[flux::spec(fn({*const[@p] i32 | p.base == p.base && p.addr == p.addr && p.size == p.size}))]
pub fn const_field_projections(_ptr: *const i32) {}

#[flux::spec(fn({*mut[@p] i32 | p.base == p.base && p.addr == p.addr && p.size == p.size}))]
pub fn mut_field_projections(_ptr: *mut i32) {}

#[flux::spec(fn(*const{p: p.base == p.base && p.addr == p.addr && p.size == p.size} i32))]
pub fn const_short_field_projections(_ptr: *const i32) {}

#[flux::spec(fn(*mut{p: p.base == p.base && p.addr == p.addr && p.size == p.size} i32))]
pub fn mut_short_field_projections(_ptr: *mut i32) {}
