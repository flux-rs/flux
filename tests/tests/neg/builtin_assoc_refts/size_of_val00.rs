use flux_attrs::*;

#[spec(fn(m: usize, size: usize) requires T::size_of_val(m) == size)]
fn requires_size<T: ?Sized>(_m: usize, size: usize) {}

trait Tr {}

fn test_slice() {
    requires_size::<[u32]>(3, 3); //~ ERROR refinement type
}

// `dyn Trait` sizes are opaque.
fn test_dyn() {
    requires_size::<dyn Tr>(0, 0); //~ ERROR refinement type
}

// Nothing is known about a generic `T: ?Sized`.
#[spec(fn(m: usize) ensures T::size_of_val(m) == 0)]
fn unsized_generic<T: ?Sized>(_m: usize) {} //~ ERROR refinement type
