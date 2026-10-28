use flux_attrs::*;

// rustc's maximum alignment, see
// https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.constraint-alignment
const MAX_ALIGN: usize = 1 << 29;

#[spec(fn() ensures T::align_of() == 0)]
fn align_zero<T>() {} //~ ERROR refinement type

#[spec(fn() ensures T::size_of() % T::align_of() != 0)]
fn size_not_multiple_of_align<T>() {} //~ ERROR refinement type

#[spec(fn() ensures T::align_of() == 6)]
fn align_not_pow2<T>() {} //~ ERROR refinement type

#[spec(fn() ensures T::size_of() > 0)]
fn size_pos<T>() {} //~ ERROR refinement type

#[spec(fn() ensures T::align_of() == 1)]
fn align_one<T>() {} //~ ERROR refinement type

#[spec(fn() ensures T::size_of() < isize::MAX)]
fn size_lt_isize_max<T>() {} //~ ERROR refinement type

#[spec(fn() ensures T::align_of() <= MAX_ALIGN / 2)]
fn align_le_2_pow_28<T>() {} //~ ERROR refinement type
