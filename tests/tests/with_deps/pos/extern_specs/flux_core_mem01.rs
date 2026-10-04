extern crate flux_core;

fn test_align_ne_zero<T>() {
    flux_rs::assert(align_of::<T>() != 0);
}

fn test_align_size_mult<T>() {
    flux_rs::assert(size_of::<T>() % align_of::<T>() == 0);
}

fn test_align_ne_pow2<T>() {
    flux_rs::assert(align_of::<T>() != 3);
    flux_rs::assert(align_of::<T>() != 5);
    flux_rs::assert(align_of::<T>() != 20);
}
