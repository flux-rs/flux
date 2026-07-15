use std::ptr::{self, NonNull};

extern crate flux_core;

flux_rs::defs! {
    fn addr_aligned(addr: int, alignment: int) -> bool { addr % alignment == 0 }
}

#[flux_rs::refined_by(base:int, addr:int, size:int, cap:int)]
#[flux_rs::invariant(size == cap * T::size_of() &&
                     cap <= isize::MAX &&
                     addr == base &&
                     T::size_of() > 0 &&
                     addr > 0 &&
                     addr_aligned(addr, T::align_of()) &&
                     addr_aligned(T::size_of(), T::align_of())
                     )]
struct RawVec<T> {
    #[flux_rs::field(NonNull<T>[base, addr, size])]
    ptr: NonNull<T>,
    #[flux_rs::field(usize[cap])]
    cap: usize,
}

#[flux_rs::refined_by(raw:RawVec, len: int)]
#[flux_rs::invariant(len <= raw.cap && addr_aligned(T::size_of(), T::align_of()))]
pub struct Vec<T> {
    #[flux_rs::field(RawVec<T>[raw])]
    buf: RawVec<T>,
    #[flux_rs::field(usize[len])]
    len: usize,
}

impl<T> Vec<T> {
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
