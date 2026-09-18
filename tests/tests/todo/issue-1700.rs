extern crate flux_core;

use std::ptr::NonNull;

// --- casts ---

#[flux_rs::spec(fn (ptr: *const [@p] T) -> Option<NonNull<T>{nn: nn.base == p.base && nn.addr == p.addr && nn.size == p.size}>)]
fn new_cast_with_match<T>(ptr: *const T) -> Option<NonNull<T>> {
    match NonNull::new(ptr as *mut T) {
        None => None,
        Some(nn) => Some(nn),
    }
}

#[flux_rs::spec(fn (ptr: *const [@p] T) -> Option<NonNull<T>{nn: nn.base == p.base && nn.addr == p.addr && nn.size == p.size}>)]
fn new_cast_with_map<T>(ptr: *const T) -> Option<NonNull<T>> {
    NonNull::new(ptr as *mut T).map(|nn| nn)
}

#[flux_rs::spec(fn (ptr: *mut [@p] T) -> Option<NonNull<T>{nn: nn.base == p.base && nn.addr == p.addr && nn.size == p.size}>)]
fn new_no_cast_with_map<T>(ptr: *mut T) -> Option<NonNull<T>> {
    NonNull::new(ptr).map(|nn| nn)
}
