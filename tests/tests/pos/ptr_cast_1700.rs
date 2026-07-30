extern crate flux_core;
use std::ptr::NonNull;

#[flux_rs::spec(fn (ptr: *const[@p] T) -> Option<NonNull<T>{nn: nn.base == p.base && nn.addr == p.addr && nn.size == p.size}>)]
fn new<T>(ptr: *const T) -> Option<NonNull<T>> {
    match NonNull::new(ptr as *mut T) {
        None => None,
        Some(nn) => Some(nn),
    }
}
