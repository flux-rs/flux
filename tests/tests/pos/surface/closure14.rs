use flux_rs::attrs::*;

// extern crate flux_core;

#[path = "../../lib/option.rs"]
mod option;

pub enum Blah {
    MkBlah(i32),
}

pub fn test00<T, F>(f: F) -> T
where
    F: FnOnce(i32) -> T,
{
    f(0)
}

// test "local" constructor
pub fn test01() -> Blah {
    test00(Blah::MkBlah)
}

// test "extern" constructor
#[spec(fn() -> Option<i32>[true])]
pub fn test02() -> Option<i32> {
    test00(Option::Some)
}
