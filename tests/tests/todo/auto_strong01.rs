/// Test to check automatically lifted strong signatures,
/// see issue https://github.com/flux-rs/flux/issues/671
use flux_rs::attrs::*;

pub struct DummyStruct {
    offset: usize,
    index: usize,
}

#[spec(fn(dummy: &mut DummyStruct) ensures dummy: DummyStruct)]
pub fn set_safe_offset(dummy: &mut DummyStruct) {
    let new_offset = if dummy.offset <= dummy.index { 0 } else { dummy.offset - dummy.index };
    dummy.offset = new_offset;
}
