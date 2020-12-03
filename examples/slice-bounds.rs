#![feature(register_tool)]
#![register_tool(liquid)]

// FIXME: add support for measures.
// FIXME: add support for immutable references.
// FIXME: add support for arrays/slices.
#[liquid::measure("fn len(s: &[u8]) -> usize")]
pub mod my_module {
    // FIXME: add support for assumptions.
    #[liquid::assume("fn(s: &[u8]) -> {x: usize | x == len(s)}")]
    fn length(slice: &[u8]) -> usize {
        slice.len()
    }

    #[liquid::assume("fn(s: &[u8], i: {i: usize | i < len(s)}) -> u8")]
    unsafe fn get_unchecked(slice: &[u8], index: usize) -> u8 {
        *slice.get_unchecked(index)
    }

    #[liquid::ty("fn(s: &[u8], i: {i: usize | i < len(s)}) -> u8")]
    pub fn get(slice: &[u8], index: usize) -> u8 {
        // FIXME: add support for function calls.
        // FIXME: add support for diverging functions.
        assert!(index < length(slice));

        unsafe { get_unchecked(slice, index) }
    }
}
