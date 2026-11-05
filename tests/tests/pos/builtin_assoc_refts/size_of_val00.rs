use flux_attrs::*;

// `MetaSized::size_of_val` / `MetaSized::align_of_val` take the pointer metadata as an argument.

#[spec(fn(m: usize, size: usize, align: usize) requires T::size_of_val(m) == size && T::align_of_val(m) == align)]
fn requires_layout<T: ?Sized>(_m: usize, size: usize, align: usize) {}

struct S {
    x: i32,
    y: i32,
}

// Sized types ignore the metadata.
fn test_sized(m: usize) {
    requires_layout::<u64>(m, 8, 8);
    requires_layout::<S>(m, 8, 4);
}

// Slices: `len * size_of::<T>()`.
fn test_slice() {
    requires_layout::<[u32]>(3, 12, 4);
    requires_layout::<[S]>(2, 16, 4);
    requires_layout::<str>(5, 5, 1);
}

// Struct with an unsized tail: the tail starts at offset 8 and the size is rounded up to the
// alignment.
struct Packet {
    tag: u64,
    data: [u8],
}

fn test_dst() {
    requires_layout::<Packet>(0, 8, 8);
    requires_layout::<Packet>(1, 16, 8);
    requires_layout::<Packet>(8, 16, 8);
    requires_layout::<Packet>(9, 24, 8);
}

// Nested unsized tail: `Packet` starts at offset 8.
struct Outer {
    flag: u8,
    packet: Packet,
}

fn test_nested_dst() {
    requires_layout::<Outer>(0, 16, 8);
    requires_layout::<Outer>(1, 24, 8);
}

// Generic `T: Sized`: `size_of_val` agrees with `size_of`.
#[spec(fn(m: usize) ensures T::size_of_val(m) == T::size_of() && T::align_of_val(m) == T::align_of())]
fn sized_generic<T>(_m: usize) {}

#[trusted]
#[spec(fn(m: usize) -> usize[T::size_of_val(m)])]
fn size_of_val<T: ?Sized>(_m: usize) -> usize {
    0
}

#[trusted]
#[spec(fn(m: usize) -> usize[T::align_of_val(m)])]
fn align_of_val<T: ?Sized>(_m: usize) -> usize {
    0
}

// Generic slices over a sized element.
#[spec(fn(m: usize) -> usize[m * T::size_of()])]
fn slice_generic_size<T>(m: usize) -> usize {
    size_of_val::<[T]>(m)
}

#[spec(fn(m: usize) -> usize[T::align_of()])]
fn slice_generic_align<T>(m: usize) -> usize {
    align_of_val::<[T]>(m)
}
