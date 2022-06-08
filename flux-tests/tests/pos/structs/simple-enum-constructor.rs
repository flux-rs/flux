#![feature(register_tool)]
#![register_tool(lr)]

pub enum MyOptionI32 {
    Some(i32),
    None,
}

pub fn test() -> MyOptionI32 {
    MyOptionI32::Some(1)
}
