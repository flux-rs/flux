extern crate flux_core;

use core::task::{RawWaker, RawWakerVTable, Waker};

unsafe fn clone_fn(data: *const ()) -> RawWaker {
    RawWaker::new(data, &VTABLE)
}
unsafe fn wake_fn(_data: *const ()) {}
unsafe fn drop_fn(_data: *const ()) {}

static VTABLE: RawWakerVTable = RawWakerVTable::new(clone_fn, wake_fn, wake_fn, drop_fn);

// --- RawWaker::new ---

#[flux::spec(fn(*const[@p] ()) -> RawWaker[p])]
pub fn test_raw_new(data: *const ()) -> RawWaker {
    RawWaker::new(data, &VTABLE)
}

// --- Waker::new ---

#[flux::spec(fn(*const[@p] ()) -> Waker[p])]
pub fn test_waker_new(data: *const ()) -> Waker {
    unsafe { Waker::new(data, &VTABLE) }
}

// --- Waker::from_raw ---

#[flux::spec(fn(RawWaker[@r]) -> Waker[r])]
pub fn test_from_raw(raw: RawWaker) -> Waker {
    unsafe { Waker::from_raw(raw) }
}

#[flux::spec(fn(*const[@p] ()) -> Waker[p])]
pub fn test_new_then_from_raw(data: *const ()) -> Waker {
    let raw = RawWaker::new(data, &VTABLE);
    unsafe { Waker::from_raw(raw) }
}

// --- Waker::noop ---

pub fn test_noop() {
    flux_rs::assert(Waker::noop().data().is_null());
}

// --- Waker::data ---

#[flux::spec(fn(&Waker[@w]) -> *const[w] ())]
pub fn test_data(w: &Waker) -> *const () {
    w.data()
}

#[flux::spec(fn(*const[@p] ()) -> *const[p] ())]
pub fn test_roundtrip(data: *const ()) -> *const () {
    let raw = RawWaker::new(data, &VTABLE);
    let w = unsafe { Waker::from_raw(raw) };
    w.data()
}
