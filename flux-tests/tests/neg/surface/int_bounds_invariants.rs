// Check that integer bound invariants are not assumed when overflow checking is disabled
#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]
#![flux::cfg(check_overflow = false)]

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

fn test00(x: i32) {
    assert(x <= i32::MAX); //~ ERROR refinement type
}

fn test01(x: i32) {
    assert(x >= i32::MIN); //~ ERROR refinement type
}

fn test02(x: u32) {
    assert(x <= u32::MAX); //~ ERROR refinement type
}

// Lower bound for unsigned integers is checked in default mode
#[allow(unused_comparisons)]
fn test03(x: u32) {
    assert(x >= 0);
}
