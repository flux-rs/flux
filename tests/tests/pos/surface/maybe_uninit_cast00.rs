use core::mem::MaybeUninit;

pub fn cast_only<T>(a: &[MaybeUninit<T>; 4]) -> *const T {
    a.as_ptr() as *const T
}
