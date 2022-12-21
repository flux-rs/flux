#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x:i32{!(x > 0)}))]
pub fn test00(x: i32) {}

pub fn test01() {
    test00(1); //~ ERROR precondition
}

#[flux::sig(fn(bool[@x], bool[!x]))]
pub fn test02(x: bool, y: bool) {}

pub fn test03() {
    test02(true, true); //~ ERROR precondition
}
