#![feature(register_tool)]
#![register_tool(flux)]

pub fn test_pass2() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}
