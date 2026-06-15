#[cfg(flux)]
use flux_attrs::*;

#[cfg(flux)]
macro_rules! ptr_specs {
    ($mutable:tt) => {
        #[extern_spec(core::ptr)]
        impl<T> *$mutable T {
            #[spec(fn (me: *$mutable[@base, @addr, @size] T, count: usize) -> *$mutable[base, addr + count, size - count] T)]
            unsafe fn add(self, count: usize) -> Self;
        }
    };
}

#[cfg(flux)]
ptr_specs!(const);

#[cfg(flux)]
ptr_specs!(mut);

#[cfg(flux)]
#[extern_spec(core::ptr)]
#[spec(fn (src: *const{p: p.addr >= p.base && p.size > 0} T) -> T)]
unsafe fn read<T>(src: *const T) -> T;

#[cfg(flux)]
#[extern_spec(core::ptr)]
#[spec(fn (dst: *mut{p: p.addr >= p.base && p.size > 0} T, src: T))]
unsafe fn write<T>(dst: *mut T, src: T);
