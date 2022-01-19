#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(bool@true) -> i32@0)]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::ty(fn() -> i32)]
pub fn unknown_int() -> i32 {
    0
}

#[lr::ty(fn() -> i32)]
pub fn free_names_before_branch() -> i32 {
    let x = unknown_int();
    if x > 0 {
        assert(x > 0);
    }
    0
}
