// Regression test for #1786: an extern spec whose associated refinement has an incompatible sort
// used to crash fixpoint when a use site (checked before the extern spec) normalized it.

extern crate flux_core;

#[flux_rs::extern_spec(core::array)]
#[flux_rs::assoc(fn succeeds(n: int, out: Result) -> bool { out.is_ok == (n == N) })] //~ ERROR implemented associated refinement `succeeds` has an incompatible sort for trait
impl<'a, T, const N: usize> TryFrom<&'a [T]> for &'a [T; N] {
    #[flux_rs::spec(fn(&[T][@n]) -> Result<&[T; N], core::array::TryFromSliceError>[n == N])]
    fn try_from(slice: &'a [T]) -> Result<&'a [T; N], core::array::TryFromSliceError>;
}

pub fn first4(s: &[u8]) -> u32 {
    let a: &[u8; 4] = s.try_into().unwrap();
    u32::from_le_bytes(*a)
}
