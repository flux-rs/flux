// Check that integer bound invariants are assumed when overflow checking is enabled
#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]
#![flux::cfg(check_overflow = true)]

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

fn test00(x: i32) {
    assert(x <= i32::MAX);
}

fn test01(x: i32) {
    assert(x >= i32::MIN);
}

fn test02(x: u32) {
    assert(x <= u32::MAX);
}

#[allow(unused_comparisons)]
fn test03(x: u32) {
    assert(x >= 0);
}
