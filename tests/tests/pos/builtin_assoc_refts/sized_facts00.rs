use flux_attrs::*;

// rustc's maximum alignment, see
// https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.constraint-alignment
const MAX_ALIGN: usize = 1 << 29;

// Facts about `T::size_of()` and `T::align_of()` that hold for every sized `T`.

#[spec(fn() ensures T::align_of() > 0)]
fn align_pos<T>() {}

#[spec(fn() ensures T::size_of() >= 0)]
fn size_nonneg<T>() {}

#[spec(fn() ensures T::size_of() % T::align_of() == 0)]
fn size_multiple_of_align<T>() {}

#[spec(fn() ensures T::align_of() != 3 && T::align_of() != 6 && T::align_of() != 20)]
fn align_pow2<T>() {}

#[spec(fn() ensures T::align_of() == 4 => T::size_of() % 4 == 0)]
fn size_multiple_of_concrete_align<T>() {}

#[spec(fn() ensures T::size_of() <= isize::MAX)]
fn size_le_isize_max<T>() {}

#[spec(fn() ensures T::align_of() <= MAX_ALIGN)]
fn align_le_max<T>() {}

#[spec(fn() ensures T::align_of() >= 2 => T::size_of() < isize::MAX)]
fn size_lt_isize_max_if_aligned<T>() {}
