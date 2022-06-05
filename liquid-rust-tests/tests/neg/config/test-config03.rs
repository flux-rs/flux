#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::cfg(fn(x: i32, y:i32) -> i32)] //~ ERROR invalid liquid configuration: bad syntax

#[lr::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}
