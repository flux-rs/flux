use flux_attrs::*;

// `size_of_val` / `align_of_val` for DSTs with tricky layouts: `repr(packed)`, `repr(align)`,
// field reordering, nested DSTs, `str` and ZST tails, and tuples. The expected values are what
// rustc computes at runtime with `size_of_val_raw` / `align_of_val_raw`.

#[spec(fn(m: usize, size: usize, align: usize) requires T::size_of_val(m) == size && T::align_of_val(m) == align)]
fn requires_layout<T: ?Sized>(_m: usize, _size: usize, _align: usize) {}

#[repr(C, packed)]
pub struct Packed { pub a: u8, pub b: u64, pub data: [u32] }
#[repr(C, packed(2))]
pub struct Packed2 { pub a: u8, pub data: [u64] }
#[repr(C, align(16))]
pub struct Aligned { pub a: u8, pub data: [u8] }
pub struct RustRepr { pub a: u8, pub b: u64, pub c: u16, pub data: [u16] }
#[repr(C)]
pub struct Inner { pub a: u32, pub data: [u8] }
#[repr(C)]
pub struct Nested { pub a: u64, pub b: u8, pub inner: Inner }
#[repr(C, packed)]
pub struct PackedNested { pub b: u8, pub inner: Inner }
pub struct StrTail { pub a: u16, pub s: str }
pub struct Zst { pub a: u8, pub data: [()] }

fn test_packed() {
    requires_layout::<Packed>(0, 9, 1);
    requires_layout::<Packed>(1, 13, 1);
    requires_layout::<Packed>(3, 21, 1);
    requires_layout::<Packed>(7, 37, 1);
}

fn test_packed2() {
    requires_layout::<Packed2>(0, 2, 2);
    requires_layout::<Packed2>(1, 10, 2);
    requires_layout::<Packed2>(3, 26, 2);
    requires_layout::<Packed2>(7, 58, 2);
}

fn test_aligned() {
    requires_layout::<Aligned>(0, 16, 16);
    requires_layout::<Aligned>(1, 16, 16);
    requires_layout::<Aligned>(3, 16, 16);
    requires_layout::<Aligned>(7, 16, 16);
}

fn test_rust_repr() {
    requires_layout::<RustRepr>(0, 16, 8);
    requires_layout::<RustRepr>(1, 16, 8);
    requires_layout::<RustRepr>(3, 24, 8);
    requires_layout::<RustRepr>(7, 32, 8);
}

fn test_nested() {
    requires_layout::<Nested>(0, 16, 8);
    requires_layout::<Nested>(1, 24, 8);
    requires_layout::<Nested>(3, 24, 8);
    requires_layout::<Nested>(7, 24, 8);
}

fn test_packed_nested() {
    requires_layout::<PackedNested>(0, 5, 1);
    requires_layout::<PackedNested>(1, 9, 1);
    requires_layout::<PackedNested>(3, 9, 1);
    requires_layout::<PackedNested>(7, 13, 1);
}

fn test_zst() {
    requires_layout::<Zst>(0, 1, 1);
    requires_layout::<Zst>(1, 1, 1);
    requires_layout::<Zst>(3, 1, 1);
    requires_layout::<Zst>(7, 1, 1);
}

fn test_str_tail() {
    requires_layout::<StrTail>(0, 2, 2);
    requires_layout::<StrTail>(1, 4, 2);
    requires_layout::<StrTail>(3, 6, 2);
    requires_layout::<StrTail>(7, 10, 2);
}

fn test_tuple() {
    requires_layout::<(u8, [u16])>(0, 2, 2);
    requires_layout::<(u8, [u16])>(1, 4, 2);
    requires_layout::<(u8, [u16])>(3, 8, 2);
    requires_layout::<(u8, [u16])>(7, 16, 2);
}
