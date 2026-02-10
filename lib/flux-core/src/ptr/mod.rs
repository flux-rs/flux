#[cfg(flux)]
use flux_attrs::*;

#[cfg(flux)]
mod const_ptr;

#[cfg(flux)]
mod mut_ptr;


#[cfg(flux)]
#[extern_spec(core::ptr)]
#[spec(fn (src: *const{p: p > 0} T) ->  T)]
fn read<T>(src: *const T) -> T;

#[cfg(flux)]
#[extern_spec(core::ptr)]
#[spec(fn (src: *const{p: p > 0} T, src: T))]
fn write<T>(src: *mut T, src: T);
