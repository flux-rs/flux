#![feature(register_tool)]
#![register_tool(liquid)]

pub struct NonZeroU32(u32);

// FIXME: add support for measures.
#[liquid::measure("fn inner(x: NonZeroU32) -> {z: u32 | z > 0}")]
pub mod my_module {
    use super::NonZeroU32;

    // FIXME: add support for user defined types.
    #[liquid::assume("fn(int: {int: u32 | u32 > 0}) -> {z: NonZeroU32 | int == inner(z)}")]
    unsafe fn new_unchecked(int: u32) -> NonZeroU32 {
        NonZeroU32(int)
    }

    #[liquid::ty("fn(int: u32) -> Option<{z: NonZeroU32 | int == inner(z)}>")]
    pub fn new(int: u32) -> Option<NonZeroU32> {
        // FIXME: add support for conditionals.
        if int > 0 {
            // FIXME: add support for function calls.
            Some(unsafe { new_unchecked(int) })
        } else {
            None
        }
    }

    #[liquid::ty("fn(x: NonZeroU32, y: {y: NonZeroU32 | inner(x) > inner(y) }) -> NonZeroU32")]
    pub fn sub(x: NonZeroU32, y: NonZeroU32) -> NonZeroU32 {
        // FIXME: add support for projections.
        unsafe { new_unchecked(x.0 + y.0) }
    }
}
