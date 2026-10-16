#![flux::opts(allow_raw_deref = "ok")]

extern crate flux_core;

static mut COUNTER: i32 = 0;

pub unsafe fn test_static_mut_write(v: i32) {
    unsafe {
        COUNTER = v;
    }
}

pub unsafe fn test_static_mut_read() -> i32 {
    unsafe { COUNTER }
}

#[flux::refined_by(p: ptr)]
pub struct Holder {
    #[flux::field(*mut[p] i32)]
    pub ptr: *mut i32,
}

#[flux::spec(fn (h: Holder[@hp], v: i32)
    requires flux_core::ptr::valid(hp, 4) && flux_core::ptr::aligned_to(hp, 4))]
pub fn test_write_through_projection(h: Holder, v: i32) {
    unsafe {
        (*h.ptr) = v;
    }
}

#[flux::spec(fn (h: Holder[@hp])
    requires flux_core::ptr::valid(hp, 4) && flux_core::ptr::aligned_to(hp, 4))]
pub fn test_addr_of_through_projection(h: Holder) {
    let _q: *mut i32 = std::ptr::addr_of_mut!(*h.ptr);
}

#[flux::spec(fn (x: *mut[@xx] i32) requires
    flux_core::ptr::valid(xx, 4) &&
    flux_core::ptr::aligned_to(xx, 4)
)]
pub fn test_addr_of_write_valid(x: *mut i32) {
    let xcopy: *mut i32 = std::ptr::addr_of_mut!(*x);
    unsafe { xcopy.write(4) }
}

pub fn test_double_deref_valid() {
    let mut v = 0;
    let p = std::ptr::addr_of_mut!(v);
    let pp: &*mut i32 = &p;
    let _r = unsafe { &mut **pp };
}
