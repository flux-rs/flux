#![flux::opts(allow_raw_deref = "ok", check_raw_deref = "true")]

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

pub struct Pair {
    pub fst: i32,
    pub snd: i32,
}

pub unsafe fn test_addr_of_field_no_use(p: *mut Pair) {
    let _q = std::ptr::addr_of_mut!((*p).fst);
}

fn x() -> i32 {
    1
}

#[flux::spec(fn (p: *mut[@pp] i32) requires
    flux_core::ptr::valid(pp, 4) && flux_core::ptr::aligned_to(pp, 4))]
pub unsafe fn test_write_through_call_dest(p: *mut i32) {
    *p = x();
}
