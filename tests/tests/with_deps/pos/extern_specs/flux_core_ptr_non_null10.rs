// `as_ref` / `as_mut` for unsized pointees, using the `meta` index and `MetaSized::size_of_val`.
extern crate flux_core;

use std::ptr::NonNull;

// Sized pointee: `size_of_val` reduces to `size_of`.
#[flux::spec(fn (nn: NonNull<u64>[@base, @addr, @size, @_meta]) -> &u64
    requires addr >= base && size >= 8 && addr % 8 == 0)]
pub fn test_as_ref_sized(nn: NonNull<u64>) -> &'static u64 {
    unsafe { nn.as_ref() }
}

// Generic sized pointee. Nothing says `T::size_of()` is non-negative, so we have to assume it.
#[flux::spec(fn (nn: NonNull<T>[@base, @addr, @size, @_meta]) -> &T
    requires addr >= base && size >= T::size_of() && addr % T::align_of() == 0 && T::size_of() >= 0)]
pub fn test_as_ref_generic<T>(nn: NonNull<T>) -> &'static T {
    unsafe { nn.as_ref() }
}

// Slice pointee: the length lives in `meta`.
#[flux::spec(fn (nn: NonNull<[u32]>[@base, @addr, @size, @meta]) -> &[u32]
    requires addr >= base && size >= 4 * meta && addr % 4 == 0)]
pub fn test_as_ref_slice(nn: NonNull<[u32]>) -> &'static [u32] {
    unsafe { nn.as_ref() }
}

// `slice_from_raw_parts` sets `meta` to the length, and `len` reads it back.
#[flux::spec(fn (data: NonNull<u32>[@base, @addr, @size, @_meta]) -> usize[3]
    requires addr >= base && size >= 12 && addr % 4 == 0)]
pub fn test_slice_len(data: NonNull<u32>) -> usize {
    NonNull::slice_from_raw_parts(data, 3).len()
}

#[flux::spec(fn (data: NonNull<u32>[@base, @addr, @size, @_meta]) -> &mut [u32]
    requires addr >= base && size >= 12 && addr % 4 == 0)]
pub fn test_slice_as_mut(data: NonNull<u32>) -> &'static mut [u32] {
    let mut nn = NonNull::slice_from_raw_parts(data, 3);
    unsafe { nn.as_mut() }
}

// A pointer from a reference covers exactly the referent, whatever its metadata, so this works for
// any `T: ?Sized` (including `dyn Trait`) without knowing the size.
pub fn test_roundtrip<T: ?Sized>(r: &mut T) -> &mut T {
    let mut nn = NonNull::from_mut(r);
    unsafe { nn.as_mut() }
}

pub trait Shape {
    fn area(&self) -> u32;
}

pub fn test_roundtrip_dyn(r: &dyn Shape) -> u32 {
    let nn = NonNull::from_ref(r);
    unsafe { nn.as_ref() }.area()
}
