extern crate flux_core;

use core::task::{RawWaker, RawWakerVTable, Waker};

unsafe fn clone_fn(data: *const ()) -> RawWaker {
    RawWaker::new(data, &VTABLE)
}
unsafe fn wake_fn(_data: *const ()) {}
unsafe fn drop_fn(_data: *const ()) {}

static VTABLE: RawWakerVTable = RawWakerVTable::new(clone_fn, wake_fn, wake_fn, drop_fn);

// --- RawWaker::new ---

#[flux::spec(fn(*const[@b, @a, @s] ()) -> RawWaker[b, a + 1, s])]
pub fn test_raw_new_wrong_addr(data: *const ()) -> RawWaker {
    RawWaker::new(data, &VTABLE) //~ ERROR refinement type
}

// --- Waker::new ---

#[flux::spec(fn(*const[@b, @a, @s] ()) -> Waker[b, a + 1, s])]
pub fn test_waker_new_wrong_addr(data: *const ()) -> Waker {
    unsafe { Waker::new(data, &VTABLE) } //~ ERROR refinement type
}

// --- Waker::from_raw ---

#[flux::spec(fn(RawWaker[@b, @a, @s]) -> Waker[b, a + 1, s])]
pub fn test_from_raw_wrong_addr(raw: RawWaker) -> Waker {
    unsafe { Waker::from_raw(raw) } //~ ERROR refinement type
}

// --- Waker::noop ---

pub fn test_noop_not_null() {
    flux_rs::assert(!Waker::noop().data().is_null()); //~ ERROR refinement type
}

#[flux::spec(fn() -> &Waker{w: w.d_base == 0})]
pub fn test_noop_base_zero() -> &'static Waker {
    Waker::noop() //~ ERROR refinement type
}

#[flux::spec(fn() -> &Waker{w: w.d_size == 0})]
pub fn test_noop_size_zero() -> &'static Waker {
    Waker::noop() //~ ERROR refinement type
}

// --- Waker::data ---

#[flux::spec(fn(&Waker[@b, @a, @s]) -> *const[b, a + 1, s] ())]
pub fn test_data_wrong_addr(w: &Waker) -> *const () {
    w.data() //~ ERROR refinement type
}

#[flux::spec(fn(*const[@b, @a, @s] ()))]
pub fn test_roundtrip_not_null(data: *const ()) {
    let raw = RawWaker::new(data, &VTABLE);
    let w = unsafe { Waker::from_raw(raw) };
    flux_rs::assert(w.data().is_null()); //~ ERROR refinement type
}
