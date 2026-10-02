extern crate flux_core;

fn test_align_eq_zero<T>() {
    flux_rs::assert(align_of::<T>() == 0); //~ ERROR refinement type
}

fn test_align_size_non_multiple<T>() {
    flux_rs::assert(size_of::<T>() % align_of::<T>() != 0); //~ ERROR refinement type
}

fn test_align_size_conc<T>() {
    if align_of::<T>() == 4 {
        flux_rs::assert(size_of::<T>() % 4 != 0); //~ ERROR refinement type
    }
}

fn test_align_ne_pow2<T>() {
    flux_rs::assert(align_of::<T>() == 3); //~ ERROR refinement type
    flux_rs::assert(align_of::<T>() == 5); //~ ERROR refinement type
    flux_rs::assert(align_of::<T>() == 20); //~ ERROR refinement type
}
