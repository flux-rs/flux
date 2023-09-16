#![feature(register_tool)]
#![register_tool(flux)]

pub fn str01() -> usize {
    let x = "str";
    x.len()
}

pub fn panic() {
    panic!("a panic")
}
