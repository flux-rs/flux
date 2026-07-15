// This test shows why the interaction of *pointer arithmetic* and *alignment* can get tricky due to *modular arithmetic*.
// See https://github.com/flux-rs/flux/pull/1686
//
// - Without `align > 0` in the `size_align_inv`, Z3 & CVC5 cannot prove the fact (perhaps it just doesn't hold?),
// - With    `align > 0` in the `size_align_inv`, and without the ensures in `fn new_add`, Z3 hangs,    CVC5 hang,
// - With    `align > 0` in the `size_align_inv`, and with    the ensures in `fn new_add`, Z3 succeeds, CVC5 hangs.
use std::ptr::{self, NonNull};

extern crate flux_core;

flux_rs::defs! {
    fn addr_aligned(addr: int, alignment: int) -> bool {
        addr % alignment == 0
    }

    fn size_align_inv(size: int, align: int) -> bool {
       addr_aligned(size, align) && align > 0
    }
}

#[flux_rs::refined_by(base:int, addr:int, size:int, cap:int)]
#[flux_rs::invariant(size == cap * T::size_of() &&
                     cap <= isize::MAX &&
                     addr == base &&
                     T::size_of() > 0 &&
                     addr > 0 &&
                     addr_aligned(addr, T::align_of()) &&
                     size_align_inv(T::size_of(), T::align_of())
                     )]
struct RawVec<T> {
    #[flux_rs::field(NonNull<T>[base, addr, size])]
    ptr: NonNull<T>,
    #[flux_rs::field(usize[cap])]
    cap: usize,
}

#[flux_rs::refined_by(raw:RawVec, len: int)]
#[flux_rs::invariant(len <= raw.cap && size_align_inv(T::size_of(), T::align_of()))]
pub struct Vec<T> {
    #[flux_rs::field(RawVec<T>[raw])]
    buf: RawVec<T>,
    #[flux_rs::field(usize[len])]
    len: usize,
}

#[flux_rs::trusted]
#[flux_rs::spec(fn (me: *mut[@p] T, count: usize)
                -> *mut[p.base, p.addr + count * T::size_of(), p.size - count * T::size_of()] T
                    requires  count * T::size_of() <= p.size
                    ensures addr_aligned(p.addr, T::align_of()) => addr_aligned(p.addr + count * T::size_of(), T::align_of())
            )]
unsafe fn new_add<T: Sized>(me: *mut T, count: usize) -> *mut T {
    unsafe { me.add(count) }
}

impl<T> Vec<T> {
    #[flux_rs::spec(fn (self: &mut Vec<T>[@me], elem: T) ensures self: Vec<T>)]
    pub fn push_new(&mut self, elem: T) {
        if self.len != self.buf.cap {
            unsafe {
                let ptr0 = self.buf.ptr.as_ptr();
                let ptr1 = new_add(ptr0, self.len);
                ptr::write(ptr1, elem);
            }
        }
    }

    #[flux_rs::spec(fn (self: &mut Vec<T>[@me], elem: T) ensures self: Vec<T>)]
    pub fn push(&mut self, elem: T) {
        if self.len != self.buf.cap {
            unsafe {
                let ptr0 = self.buf.ptr.as_ptr();
                let ptr1 = ptr0.add(self.len);
                ptr::write(ptr1, elem);
            }
        }
    }
}
